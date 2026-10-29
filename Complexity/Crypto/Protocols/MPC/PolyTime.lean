/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.Composition
public import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation
public import Complexity.Computability.Probabilistic.Oracle.Composition
public import Complexity.Languages.Probabilistic.Oracle.Interaction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Probabilistic.Adaptive
import Complexity.Computability.Probabilistic.Finite
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Polynomial-Time Completeness of $\text{OT}_1^4$ for Semi-Honest Multi-Party Computation

This module formalizes a proper-coalition variant of Goldreich's semi-honest multi-party
completeness theorem for 1-out-of-4 bit oblivious transfer $\text{OT}_1^4$ (Section 7.5.2.4,
Theorem 7.5.12, print p. 707; generalizing Section 7.3.4, Theorem 7.3.11, print p. 648), with
uniform efficiency certificates for the joint word-level runner and coalition simulators.
Given any polynomial-time computable family of $m$-party randomized functionalities specified
by a word-level evaluator
`F : α × List Bool → List Bool` with polynomial-time unary input width `n : α → ℕ`, output width
`k : α → ℕ`, and shared-coin width `coins : α → ℕ`:

1. **Uniform Circuit Compilation:** `Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily`
   compiles `F` into a polynomial-time constructible family of Boolean circuits
   `C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)` whose evaluation agrees
   with `wordRandomizedFunctionality m coins n k F a`.
2. **Word-Level Protocol Execution & Bridge Lemma:** `Protocol.runEncoded` executes any
   `ot14Spec`-hybrid protocol in `Cslib.Probability.WordOracleComp Unit (List Bool)` by translating
   each typed `ot14Spec` query to a 6-bit word query and reading the 1-bit reply prefix.
   `Protocol.eval_runEncoded_eq_evalWith_map` proves that running `Π.runEncoded` against
   `ot14WordHandler` yields the exact distribution of `(Π.evalWith ot14World x).map
   (encodeViewsAndOutputs encView encOut)`.
3. **Uniform Efficiency Certificates:** Over `Sigma`-packaged family inputs `FamilyRunInput` and
   `FamilySimInput`, `isOraclePPTOn_gmwOT14RandomizedProtocol` certifies that the centralized joint
   word-encoded execution `Protocol.runEncoded` of `gmwOT14RandomizedProtocol` across all `m`
   parties is `Cslib.Probability.IsOraclePPTOn` (note that this certifies the joint word-level
   runner rather than separate per-party local PPT strategies), and
   `isPPTOn_gmwOT14RandomizedSim` certifies that for every static coalition `I : Finset (Fin m)`,
   the encoded view simulator `gmwOT14RandomizedSim` is `Cslib.Probability.IsPPTOn`. Because
   `gmwCircuitProtocol` (Construction 7.5.10, p. 706) includes one `sharedMulSpec m` share-refresh
   call per output coordinate `(r, j) : Fin m × Fin k a` in Step 3 in addition to one call per
   `.and`/`.or` gate in Step 2, composing with `multiPartyMulProtocol m` (Construction 7.5.8,
   p. 704) and `twoPartyMulProtocol` (Construction 7.3.7, pp. 643–644) expands each
   `sharedMulSpec m` call into $m(m-1)/2$ pairwise `ot14Spec` calls (adding
   $m \cdot k(a) \cdot m(m-1)/2$ calls in Step 3, polynomial in
   $m, n(a), k(a), (C\,a).\text{size}$).
4. **End-to-End Completeness (`exists_perfectSemiHonestPrivate_ot14_of_polyTime`):** Formalizes a
   **proper-coalition variant** of Goldreich's Theorem 7.5.12, combining uniform circuit
   compilation, proper-coalition perfect semi-honest privacy in `ot14World`
   (`PerfectSemiHonestPrivateProper`), and uniform `IsOraclePPTOn` / `IsPPTOn` efficiency. The
   proper-coalition quantifier `I ≠ Finset.univ` is narrower than Goldreich's Definition 7.5.1 and
   Theorem 7.5.12 (which quantify over all `I ⊆ [m]`, p. 696; Goldreich's text on pp. 697 and 703
   treats `I = [m]` as trivial without restricting that remark to deterministic functionalities or
   to the view-only Eq. 7.39). Under the joint view-and-output equation Eq. 7.40 for randomized
   functionalities, `I = Finset.univ` is not vacuous: the canonical independent-coin-share simulator
   `randomizedWrapperSim` is refuted at `I = Finset.univ` by
   `not_perfectSemiHonestPrivate_coinEchoRandomizedWrapper_univ` in
   [ComplexityTests/Crypto/MPC.lean](https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/Crypto/MPC.lean),
   and any full-coalition simulator receiving only `(x, y)` would have to sample coin shares whose
   XOR `r` satisfies `g(r, x) = y`.

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
* `Cslib.Crypto.Protocols.MPC.FamilyRunInput`, `Cslib.Crypto.Protocols.MPC.FamilySimInput`,
  `Cslib.Crypto.Protocols.MPC.encFamilyRunInput`, `Cslib.Crypto.Protocols.MPC.encFamilySimInput`:
  `Sigma`-packaged family input records and injective bit-list encodings.
* `Cslib.Crypto.Protocols.MPC.encGMWPartyView`, `Cslib.Crypto.Protocols.MPC.encodeCoalitionView`:
  word-level view encoders for `gmwOT14RandomizedProtocol` and `gmwOT14RandomizedSim`.

## Main results

* `Cslib.Crypto.Protocols.MPC.Steps.runWith_runEncoded_eq_evalWith`,
  `Cslib.Crypto.Protocols.MPC.Protocol.eval_runEncoded_eq_evalWith_map`: bridge lemmas relating
  `Steps.runEncoded` / `Protocol.runEncoded` under `ot14WordHandler` to `evalWith ot14World`.
* `Cslib.Crypto.Protocols.MPC.isOraclePPTOn_gmwOT14RandomizedProtocol`: uniform `IsOraclePPTOn`
  certificate for the joint word-level runner `Protocol.runEncoded` applied to
  `gmwOT14RandomizedProtocol`.
* `Cslib.Crypto.Protocols.MPC.isPPTOn_gmwOT14RandomizedSim`: uniform `IsPPTOn` certificate for
  `gmwOT14RandomizedSim`.
* `Cslib.Crypto.Protocols.MPC.exists_perfectSemiHonestPrivate_ot14_of_polyTime`: proper-coalition
  variant of Theorem 7.5.12 (Section 7.5.2.4, print p. 707; generalizing Theorem 7.3.11, Section
  7.3.4, print p. 648), establishing polynomial-time completeness of $\text{OT}_1^4$ for $m$-party
  semi-honest computation against every proper coalition `I ≠ Finset.univ`.

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

@[simp] private theorem Steps.runEncoded_mapState {m : ℕ} {State State' Out : Fin m → Type}
    {sc : Schedule m ot14Spec} (f : (i : Fin m) → State i → State' i)
    (steps : Steps State' Out sc) (st : (i : Fin m) → State i) :
    (steps.mapState f).runEncoded st = steps.runEncoded (fun i => f i (st i)) := by
  induction steps generalizing State with
  | done output => rfl
  | message send next ih =>
    simp [Steps.mapState, Steps.runEncoded, ih]
  | oracle query next ih =>
    simp [Steps.mapState, Steps.runEncoded, ih]

@[simp] private theorem Steps.runEncoded_append {m : ℕ} {State Mid Out : Fin m → Type}
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

@[simp] private theorem Steps.runEncoded_embed {k m : ℕ} (parties : Fin k ↪ Fin m)
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

/-! ### Part 2: `Sigma`-Packaged Family Input Encodings and `encGMWPartyView` -/

/-- `Sigma`-packaged input record for executing a protocol family at instance `a : α`. -/
abbrev FamilyRunInput (α : Type) (m : ℕ) (n : α → ℕ) :=
  Σ a : α, Fin m → BitString (n a)

/-- `Sigma`-packaged input record for running the coalition simulator at instance `a : α`. -/
abbrev FamilySimInput (α : Type) (m : ℕ) (n k : α → ℕ) (I : Finset (Fin m)) :=
  Σ a : α, ((i : I) → BitString (n a)) × ((i : I) → BitString (k a))

/-- Injective bit-list encoding of `FamilyRunInput α m n`: pairs `enc a` with the packed `m * n a`
party input bits `List.ofFn (BitString.blocksEquiv.symm x)`. -/
@[expose] def encFamilyRunInput {α : Type} (enc : α ↪ List Bool) (m : ℕ) (n : α → ℕ) :
    FamilyRunInput α m n ↪ List Bool where
  toFun inp :=
    encPair enc encBits
      (inp.1,
       List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n inp.1)).symm inp.2))
  inj' := by
    rintro ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h
    obtain ⟨ha, hx⟩ := Prod.ext_iff.1 ((encPair enc encBits).injective h)
    dsimp only at ha hx
    subst ha
    have hx' := List.ofFn_injective hx
    exact Sigma.ext rfl (heq_of_eq (Cslib.BitString.blocksEquiv.symm.injective hx'))

/-- Pad a coalition-indexed bitstring tuple `vI : (i : I) → BitString len` with `0` outside `I`
and serialize the resulting `m` blocks of width `len` to a `m * len`-bit list. -/
private def extendCoalitionBits {m len : ℕ} (I : Finset (Fin m)) (vI : (i : I) → BitString len) :
    List Bool :=
  List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := len)).symm
    (GMWCircuit.extendByZero I vI))

private theorem extendCoalitionBits_injective {m len : ℕ} (I : Finset (Fin m)) :
    Function.Injective (extendCoalitionBits (len := len) I) := by
  intro u v h
  have h1 := Cslib.BitString.blocksEquiv.symm.injective (List.ofFn_injective h)
  ext ⟨i, hi⟩ j
  have hi_eq := congrFun h1 i
  simp only [GMWCircuit.extendByZero, hi, ↓reduceDIte] at hi_eq
  exact congrFun hi_eq j

/-- Injective bit-list encoding of `FamilySimInput α m n k I`: pairs `enc a` with the zero-extended
packed coalition input bits `extendCoalitionBits I xI` and output bits
`extendCoalitionBits I yI`. -/
def encFamilySimInput {α : Type} (enc : α ↪ List Bool) (m : ℕ) (n k : α → ℕ)
    (I : Finset (Fin m)) : FamilySimInput α m n k I ↪ List Bool where
  toFun inp :=
    encPair enc (encPair encBits encBits)
      (inp.1, (extendCoalitionBits I inp.2.1, extendCoalitionBits I inp.2.2))
  inj' := by
    rintro ⟨a₁, x₁, y₁⟩ ⟨a₂, x₂, y₂⟩ h
    obtain ⟨ha, hxy⟩ := Prod.ext_iff.1 ((encPair enc (encPair encBits encBits)).injective h)
    dsimp only at ha hxy
    subst ha
    obtain ⟨hx, hy⟩ := Prod.ext_iff.1 hxy
    dsimp only at hx hy
    rw [extendCoalitionBits_injective I hx, extendCoalitionBits_injective I hy]

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
`GMWCircuit.msgSchedule (BitString N) L`. -/
private def encPairsMsgReceived {m N : ℕ} (i : Fin m) :
    (L : List (Fin m × Fin m)) →
      (otMulCompose (GMWCircuit.msgSchedule (spec := sharedMulSpec m) (BitString N) L)).Received i →
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
  encPair
    (encPair (encPair encBits encBits) (encPair encBits encBits))
    (encPair encBits (encPair encBits encBits))
    (((List.ofFn v.input, List.ofFn v.coins.1),
      (List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm v.coins.2.1.1),
       encOTSubCoins _ i v.coins.2.2)),
     (encPairsMsgReceived i (GMWCircuit.allPairs m) r_in,
      (encOTOracleAnswers _ i v.received,
       encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) r_out)))

/-- Encode a coalition view tuple `vI : (i : I) → PartyView In Coins sc i.1` into `List Bool`
by listing `encView i (vI ⟨i, hi⟩)` for `i ∈ I` and `[]` for `i ∉ I`. -/
@[expose] def encodeCoalitionView {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins : Fin m → Type}
    (encView : (i : Fin m) → PartyView In Coins sc i → List Bool)
    (I : Finset (Fin m)) (vI : (i : I) → PartyView In Coins sc i.1) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i => if hi : i ∈ I then encView i (vI ⟨i, hi⟩) else [])

/-! ### Part 3: Uniform Polynomial-Time Compilation of `xorPreludeCircuit` -/

namespace XORPreludeCode

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Raw circuit code of `XORPrelude.xorBitAtCircuit coins c`. -/
private def xorBitAtCode (coins c : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([(.or, [c, c + coins]),
    (.and, [c, c + coins]),
    (.not, [(coins + coins) + 1]),
    (.and, [coins + coins, (coins + coins) + 2])],
   [(coins + coins) + 3])

private theorem code_xorBitAtCircuit (coins : ℕ) (c : Fin coins) :
    (XORPrelude.xorBitAtCircuit coins c).code = xorBitAtCode coins c.val := by
  simp [XORPrelude.xorBitAtCircuit, Program.appendXor, Circuit.code, Line.code, xorBitAtCode,
    Nat.add_comm]

/-- Raw circuit code of `XORPrelude.zeroBitStringCircuit w coins`. -/
private def zeroBitStringCode (w coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([(.const false, [])], List.replicate coins w)

private theorem code_zeroBitStringCircuit (w coins : ℕ) :
    (XORPrelude.zeroBitStringCircuit w coins).code = zeroBitStringCode w coins := by
  simp [XORPrelude.zeroBitStringCircuit, Circuit.code, Line.code, zeroBitStringCode]

/-- Raw circuit code of `XORPrelude.xorBitStringsCircuit coins`. -/
private def xorBitStringsCode (coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  bundleCode (coins + coins) 4 ((List.range coins).map (xorBitAtCode coins))

private theorem code_xorBitStringsCircuit (coins : ℕ) :
    (XORPrelude.xorBitStringsCircuit coins).code = xorBitStringsCode coins := by
  have hmap : (List.range coins).map (xorBitAtCode coins) =
      List.ofFn (fun c : Fin coins => (XORPrelude.xorBitAtCircuit coins c).code) := by
    refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
    simp [code_xorBitAtCircuit]
  rw [XORPrelude.xorBitStringsCircuit, xorBitStringsCode, hmap,
    bundleCode_code (XORPrelude.xorBitAtCircuit coins) 4 (fun _ => rfl)]

/-- Raw circuit code of `XORPrelude.sumBlocksCircuit m coins`. -/
private def sumBlocksCode : (m coins : ℕ) → List (Boolean.Op × List ℕ) × List ℕ
  | 0, coins => zeroBitStringCode (0 * coins) coins
  | m + 1, coins =>
    compCode ((m + 1) * coins) (xorBitStringsCode coins)
      (appendCode ((m + 1) * coins)
        (compCode ((m + 1) * coins) (sumBlocksCode m coins)
          ([], List.range (m * coins)))
        ([], (List.range coins).map (fun c => c + coins * m)))

private theorem code_sumBlocksCircuit (m coins : ℕ) :
    (XORPrelude.sumBlocksCircuit m coins).code = sumBlocksCode m coins := by
  induction m with
  | zero =>
    simpa [XORPrelude.sumBlocksCircuit, sumBlocksCode] using
      code_zeroBitStringCircuit (0 * coins) coins
  | succ m ih =>
    have hw₁ :
        (Circuit.wiring Boolean.signature
          (Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m)))).code =
        ([], List.range (m * coins)) := by
      simpa using Circuit.code_wiring_eq_map (σ := Boolean.signature)
        (f := Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m))) (g := id) fun _ => rfl
    have hw₂ :
        (Circuit.wiring Boolean.signature
          (fun c : Fin coins => finProdFinEquiv (Fin.last m, c))).code =
        ([], (List.range coins).map (fun c => c + coins * m)) :=
      Circuit.code_wiring_eq_map fun c => by simp [finProdFinEquiv_apply_val]
    simp only [XORPrelude.sumBlocksCircuit, sumBlocksCode, ← compCode_code, ← appendCode_code,
      code_xorBitStringsCircuit, ih, hw₁, hw₂]

/-- Raw circuit code of `XORPrelude.extractInputsCircuit m n coins`. -/
private def extractInputsCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([], (List.range (m * n)).map fun idx => idx % n + (n + coins) * (idx / n))

private theorem code_extractInputsCircuit (m n coins : ℕ) :
    (XORPrelude.extractInputsCircuit m n coins).code = extractInputsCode m n coins :=
  Circuit.code_wiring_eq_map fun idx => by
    simp [finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply]

/-- Raw circuit code of `XORPrelude.extractCoinsCircuit m n coins`. -/
private def extractCoinsCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([], (List.range (m * coins)).map fun idx => (n + idx % coins) + (n + coins) * (idx / coins))

private theorem code_extractCoinsCircuit (m n coins : ℕ) :
    (XORPrelude.extractCoinsCircuit m n coins).code = extractCoinsCode m n coins :=
  Circuit.code_wiring_eq_map fun idx => by
    simp [finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply]

/-- Raw circuit code of `xorPreludeCircuit m n coins`. -/
private def xorPreludeCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  appendCode (m * (n + coins))
    (extractInputsCode m n coins)
    (compCode (m * (n + coins)) (sumBlocksCode m coins) (extractCoinsCode m n coins))

private theorem code_xorPreludeCircuit (m n coins : ℕ) :
    (xorPreludeCircuit m n coins).code = xorPreludeCode m n coins := by
  simp only [xorPreludeCircuit, xorPreludeCode, ← appendCode_code, ← compCode_code,
    code_extractInputsCircuit, code_sumBlocksCircuit, code_extractCoinsCircuit]

private theorem computableTidilyInPolyTime_xorBitAtCode {α : Type} {enc : α ↪ List Bool}
    {coins c : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encNat)
    (hc : ComputableTidilyInPolyTime c enc encNat) :
    ComputableTidilyInPolyTime (fun a => xorBitAtCode (coins a) (c a)) enc encCode := by
  unfold xorBitAtCode
  fun_prop

private theorem computableTidilyInPolyTime_zeroBitStringCode {α : Type} {enc : α ↪ List Bool}
    {w coins : α → ℕ}
    (hw : ComputableTidilyInPolyTime w enc encNat)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => zeroBitStringCode (w a) (coins a)) enc encCode := by
  unfold zeroBitStringCode
  fun_prop

private theorem computableTidilyInPolyTime_xorBitStringsCode {α : Type} {enc : α ↪ List Bool}
    {coins : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => xorBitStringsCode (coins a)) enc encCode := by
  have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
  have htwoCoins : ComputableTidilyInPolyTime (fun a => coins a + coins a) enc encNat := by
    fun_prop
  have hbit : ComputableTidilyInPolyTime
      (fun p : α × ℕ => xorBitAtCode (coins p.1) p.2)
      (encPair enc encUnary) encCode :=
    computableTidilyInPolyTime_xorBitAtCode
      (hcoinsBin.comp (fst enc encUnary))
      (unary_to_binary.comp (snd enc encUnary))
  exact (computableInPolyTime_bundleCode (.of_tidy htwoCoins) (.of_tidy (const 4))
    (.of_tidy (mapWith hbit id' (range.comp hcoins)))).tidy

private theorem computableTidilyInPolyTime_sumBlocksCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {coins : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => sumBlocksCode m (coins a)) enc encCode := by
  induction m with
  | zero =>
    have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
    have hw : ComputableTidilyInPolyTime (fun a => 0 * coins a) enc encNat := by fun_prop
    exact computableTidilyInPolyTime_zeroBitStringCode hw hcoins
  | succ m ih =>
    have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
    have hmCoinsUnary : ComputableTidilyInPolyTime (fun a => m * coins a) enc encUnary := by
      polytime
    have hsuccCoinsBin : ComputableTidilyInPolyTime (fun a => (m + 1) * coins a) enc encNat := by
      fun_prop
    have hrange₁ : ComputableTidilyInPolyTime
        (fun a => ([], List.range (m * coins a))) enc encCode := by
      have hr : ComputableTidilyInPolyTime
          (fun a => List.range (m * coins a)) enc (encList encNat) := by
        simpa only [Function.comp_def, List.map_id'] using
          unary_to_binary.map.comp (range.comp hmCoinsUnary)
      exact (const []).prod hr
    have hrange₂ : ComputableTidilyInPolyTime
        (fun a => ([], (List.range (coins a)).map (fun c => c + coins a * m))) enc encCode := by
      have hp1 : ComputableTidilyInPolyTime (fun p : α × ℕ => coins p.1)
          (encPair enc encUnary) encNat := hcoinsBin.comp (fst enc encUnary)
      have hp2 : ComputableTidilyInPolyTime (fun p : α × ℕ => p.2)
          (encPair enc encUnary) encNat := unary_to_binary.comp (snd enc encUnary)
      have hf : ComputableTidilyInPolyTime (fun p : α × ℕ => p.2 + coins p.1 * m)
          (encPair enc encUnary) encNat := by fun_prop
      exact (const []).prod (mapWith hf id' (range.comp hcoins))
    exact (computableInPolyTime_compCode (.of_tidy hsuccCoinsBin)
      (.of_tidy (computableTidilyInPolyTime_xorBitStringsCode hcoins))
      (computableInPolyTime_appendCode (.of_tidy hsuccCoinsBin)
        (computableInPolyTime_compCode (.of_tidy hsuccCoinsBin) (.of_tidy ih) (.of_tidy hrange₁))
        (.of_tidy hrange₂))).tidy

private theorem computableTidilyInPolyTime_extractInputsCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => extractInputsCode m (n a) (coins a)) enc encCode := by
  have hnBin : ComputableTidilyInPolyTime n enc encNat := unary_to_binary.comp hn
  have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
  have hmn : ComputableTidilyInPolyTime (fun a => m * n a) enc encUnary := by polytime
  have hp_n : ComputableTidilyInPolyTime (fun p : α × ℕ => n p.1)
      (encPair enc encUnary) encNat := hnBin.comp (fst enc encUnary)
  have hp_coins : ComputableTidilyInPolyTime (fun p : α × ℕ => coins p.1)
      (encPair enc encUnary) encNat := hcoinsBin.comp (fst enc encUnary)
  have hp_idx : ComputableTidilyInPolyTime (fun p : α × ℕ => p.2)
      (encPair enc encUnary) encNat := unary_to_binary.comp (snd enc encUnary)
  have hf : ComputableTidilyInPolyTime
      (fun p : α × ℕ => p.2 % n p.1 + (n p.1 + coins p.1) * (p.2 / n p.1))
      (encPair enc encUnary) encNat := by fun_prop
  exact (const []).prod (mapWith hf id' (range.comp hmn))

private theorem computableTidilyInPolyTime_extractCoinsCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => extractCoinsCode m (n a) (coins a)) enc encCode := by
  have hnBin : ComputableTidilyInPolyTime n enc encNat := unary_to_binary.comp hn
  have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
  have hmc : ComputableTidilyInPolyTime (fun a => m * coins a) enc encUnary := by polytime
  have hp_n : ComputableTidilyInPolyTime (fun p : α × ℕ => n p.1)
      (encPair enc encUnary) encNat := hnBin.comp (fst enc encUnary)
  have hp_coins : ComputableTidilyInPolyTime (fun p : α × ℕ => coins p.1)
      (encPair enc encUnary) encNat := hcoinsBin.comp (fst enc encUnary)
  have hp_idx : ComputableTidilyInPolyTime (fun p : α × ℕ => p.2)
      (encPair enc encUnary) encNat := unary_to_binary.comp (snd enc encUnary)
  have hf : ComputableTidilyInPolyTime
      (fun p : α × ℕ => (n p.1 + p.2 % coins p.1) + (n p.1 + coins p.1) * (p.2 / coins p.1))
      (encPair enc encUnary) encNat := by fun_prop
  exact (const []).prod (mapWith hf id' (range.comp hmc))

private theorem computableTidilyInPolyTime_xorPreludeCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => xorPreludeCode m (n a) (coins a)) enc encCode := by
  have hnBin : ComputableTidilyInPolyTime n enc encNat := unary_to_binary.comp hn
  have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
  have hwidth : ComputableTidilyInPolyTime (fun a => m * (n a + coins a)) enc encNat := by
    fun_prop
  exact (computableInPolyTime_appendCode (.of_tidy hwidth)
    (.of_tidy (computableTidilyInPolyTime_extractInputsCode m hn hcoins))
    (computableInPolyTime_compCode (.of_tidy hwidth)
      (.of_tidy (computableTidilyInPolyTime_sumBlocksCode m hcoins))
      (.of_tidy (computableTidilyInPolyTime_extractCoinsCode m hn hcoins)))).tidy

end XORPreludeCode

/-- The circuit code of `xorPreludeCircuit m (n a) (coins a)` is constructible in uniform
polynomial time from `a : α`. -/
private theorem computableInPolyTime_code_xorPreludeCircuit {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableInPolyTime n enc Turing.MultiTapeTM.encUnary)
    (hcoins : ComputableInPolyTime coins enc Turing.MultiTapeTM.encUnary) :
    ComputableInPolyTime (fun a => (xorPreludeCircuit m (n a) (coins a)).code)
      enc Boolean.encCode :=
  .of_tidy
    ((XORPreludeCode.computableTidilyInPolyTime_xorPreludeCode m hn.tidy hcoins.tidy).of_enc_eq
      fun a => by rw [XORPreludeCode.code_xorPreludeCircuit])

/-- Composing a polynomial-time constructible circuit family `C a` with `xorPreludeCircuit` yields
a polynomial-time constructible circuit family
`(C a).comp (xorPreludeCircuit m (n a) (coins a))`. -/
private theorem computableInPolyTime_code_comp_xorPreludeCircuit {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins k : α → ℕ}
    {C : (a : α) → Cslib.Circuits.Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hn : ComputableInPolyTime n enc Turing.MultiTapeTM.encUnary)
    (hcoins : ComputableInPolyTime coins enc Turing.MultiTapeTM.encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode) :
    ComputableInPolyTime
      (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code)
      enc Boolean.encCode := by
  have hnBin : Turing.MultiTapeTM.ComputableTidilyInPolyTime n enc Turing.MultiTapeTM.encNat :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary.comp hn.tidy
  have hcoinsBin :
      Turing.MultiTapeTM.ComputableTidilyInPolyTime coins enc Turing.MultiTapeTM.encNat :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary.comp hcoins.tidy
  have hwidth : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a => m * (n a + coins a)) enc Turing.MultiTapeTM.encNat := by
    fun_prop
  have hcomp := (Boolean.computableInPolyTime_compCode (.of_tidy hwidth) hC
    (computableInPolyTime_code_xorPreludeCircuit m hn hcoins)).tidy
  exact .of_tidy (hcomp.of_enc_eq fun a => by rw [Boolean.compCode_code])

/-! ### Part 4: Bounded-Growth Monadic List Folds and Word-Level Efficiency -/

namespace PolyTimeRunner

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Binary encoding of `Fin m` via `Fin.val`. -/
private def encFin (m : ℕ) : Fin m ↪ List Bool :=
  Function.Embedding.trans ⟨Fin.val, Fin.val_injective⟩ encNat

private theorem length_encList_tail_le {Item : Type} (enc : Item ↪ List Bool)
    (L : List Item) :
    (encList enc L.tail).length ≤ (encList enc L).length := by
  cases L with
  | nil => rfl
  | cons x rest =>
    simp [encList_cons]

private theorem length_encList_ofFn_le {n : ℕ} (u v : Fin n → List Bool) (d : ℕ)
    (h : ∀ i : Fin n, (v i).length ≤ (u i).length + d) :
    (encList encBits (List.ofFn v)).length ≤
      (encList encBits (List.ofFn u)).length + n * (2 * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 := h 0
    have hs := ih (fun i => u i.succ) (fun i => v i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, encList_cons, List.length_append, length_frame,
      encBits_apply, Nat.add_mul, Nat.one_mul]
    omega

private theorem length_encPi_encBits_le {m : ℕ} (f g : Fin m → List Bool) (d : ℕ)
    (h : ∀ i : Fin m, (g i).length ≤ (f i).length + d) :
    (encPi encBits g).length ≤ (encPi encBits f).length + m * (2 * d) := by
  simpa only [encPi_apply, Fintype.card_fin] using
    length_encList_ofFn_le
      (fun i => f ((Fintype.equivFin (Fin m)).symm i))
      (fun i => g ((Fintype.equivFin (Fin m)).symm i))
      d (fun i => h _)

private theorem computableTidilyInPolyTime_ofList_fin (d : ℕ) :
    ComputableTidilyInPolyTime (Cslib.BitString.ofList d) encBits (encPi encBool) := by
  refine pi fun k => ?_
  change ComputableTidilyInPolyTime
    ((fun p : List Bool × ℕ => p.1.getD p.2 false) ∘ fun w => (w, k.val)) encBits encBool
  exact (listGetD false).comp (id'.prod (const k.val))

/-- Sampling a uniform function `ι → Bool` from any finite index type `[Fintype ι]` is strict PPT
for any fixed input and output encodings. -/
private theorem isPPTOn_uniform_fintype_bool {α ι : Type} [Fintype ι] [DecidableEq ι]
    (input : α ↪ List Bool) (output : (ι → Bool) ↪ List Bool) :
    IsPPTOn input output (fun _ => ProbComp.uniform (ι → Bool)) := by
  let card := Fintype.card ι
  let e : ι ≃ Fin card := Fintype.equivFin ι
  let toMap : (Fin card → Bool) → (ι → Bool) := fun f i => f (e i)
  let decode : List Bool → (ι → Bool) := fun w => toMap (Cslib.BitString.ofList card w)
  have hdecode : ComputableTidilyInPolyTime decode encBits output :=
    (of_finite (encA := encPi encBool) (encB := output) toMap).comp
      (computableTidilyInPolyTime_ofList_fin card)
  have hseeded : IsPPTOn input output (fun _ : α => decode <$> Cslib.BitString.sampleList card) :=
    IsPPTOn.of_seeded (.of_tidy (const card))
      (.of_tidy (hdecode.comp (snd input encBits)))
  refine hseeded.congr fun _ => ?_
  rw [ProbComp.eval_map, Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    PMF.map_comp, ProbComp.eval_uniform]
  have heq : decode ∘ List.ofFn = Equiv.piCongrLeft' (fun _ => Bool) e.symm := by
    funext f
    ext i
    simp [decode, toMap, Cslib.BitString.ofList_ofFn, Equiv.piCongrLeft']
  rw [heq, PMF.uniformOfFintype_map_equiv]

/-- Sampling `m` independent bit lists of polynomial-time unary lengths `len a i` is strict PPT. -/
private theorem isPPTOn_pi_sampleList {α : Type} {input : α ↪ List Bool}
    (m : ℕ) {len : α → Fin m → ℕ}
    (hlen : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => len a i) input encUnary) :
    IsPPTOn input (encPi encBits)
      (fun a => OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i))) := by
  induction m with
  | zero =>
    have hpure : IsPPTOn input (encPi encBits) (fun _ : α => pure Fin.elim0) :=
      (pi fun i : Fin 0 => i.elim0).isPPTOn
    refine hpure.congr fun a => ?_
    ext f
    simp [Subsingleton.elim f Fin.elim0]
  | succ m ih =>
    have h0 : IsPPTOn input encBits (fun a => Cslib.BitString.sampleList (len a 0)) :=
      (ComputableInPolyTime.of_tidy (hlen 0)).sampleList
    have hrest : IsPPTOn input (encPi encBits)
        (fun a => OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i.succ))) :=
      ih (fun i => hlen i.succ)
    have hcomb : ComputableTidilyInPolyTime
        (fun p : List Bool × (Fin m → List Bool) => Fin.cons p.1 p.2)
        (encPair encBits (encPi encBits)) (encPi encBits) := by
      refine pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact fst _ _
      · exact (pi_apply encBits j).comp (snd _ _)
    have hsecond : IsPPTOn (encPair input encBits) (encPair encBits (encPi encBits))
        (fun pair : α × List Bool =>
          (fun xs => (pair.2, xs)) <$>
            OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len pair.1 i.succ))) :=
      (hrest.preprocess (.of_tidy (fst input encBits))).pair (snd input encBits)
    have hbind :=
      (h0.bind_with (second := fun a x0 =>
        (fun xs => (x0, xs)) <$>
          OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i.succ)))
        hsecond).map (.of_tidy hcomb)
    refine hbind.congr fun a => ?_
    rw [OracleComp.pi_succ]
    simp [ProbComp.eval_bind, ProbComp.eval_map]

/-- Left monadic fold over a list in `OracleComp spec`. -/
private def foldlMList {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (singleStep : Item → Acc → OracleComp spec Acc) :
    List Item → Acc → OracleComp spec Acc
  | [], acc => pure acc
  | x :: rest, acc => do
    let acc' ← singleStep x acc
    foldlMList singleStep rest acc'

@[simp] private theorem foldlMList_nil {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (singleStep : Item → Acc → OracleComp spec Acc) (acc : Acc) :
    foldlMList singleStep [] acc = pure acc := rfl

@[simp] private theorem foldlMList_cons {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (singleStep : Item → Acc → OracleComp spec Acc) (x : Item) (rest : List Item) (acc : Acc) :
    foldlMList singleStep (x :: rest) acc = (do
      let acc' ← singleStep x acc
      foldlMList singleStep rest acc') := rfl

@[simp] private theorem foldlMList_append {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (singleStep : Item → Acc → OracleComp spec Acc) (L₁ L₂ : List Item) (acc : Acc) :
    foldlMList singleStep (L₁ ++ L₂) acc = (do
      let acc₁ ← foldlMList singleStep L₁ acc
      foldlMList singleStep L₂ acc₁) := by
  induction L₁ generalizing acc with
  | nil => simp
  | cons x rest ih => simp [ih, bind_assoc]

/-- Single iteration step on `List Item × Acc` that consumes the head element (with `fallback` on
`[]`) and advances to `tail`. -/
private def stepList {ι : Type} {spec : OracleSpec ι} {Item Acc : Type} (fallback : Item)
    (singleStep : Item → Acc → OracleComp spec Acc)
    (st : List Item × Acc) : OracleComp spec (List Item × Acc) :=
  (fun acc' => (st.1.tail, acc')) <$> singleStep (st.1.headD fallback) st.2

private theorem iterate_stepList_eq_foldlMList {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (fallback : Item) (singleStep : Item → Acc → OracleComp spec Acc)
    (L : List Item) (acc : Acc) :
    Prod.snd <$> OracleComp.iterate L.length (stepList fallback singleStep) (L, acc) =
      foldlMList singleStep L acc := by
  induction L generalizing acc with
  | nil => simp [foldlMList]
  | cons x rest ih =>
    simp [List.length_cons, OracleComp.iterate_succ_bind, stepList, foldlMList,
      ← ih, map_bind, bind_map_left]

/-- Certify a monadic list fold `foldlMList singleStep (list a) (init a)` in `WordOracleComp`
from a constant growth bound on the accumulator encoding `encAcc`. -/
private theorem isOraclePPTOn_foldlMList_of_bounded_growth
    {Operation α Item Acc : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {encItem : Item ↪ List Bool} {encAcc : Acc ↪ List Bool}
    (fallback : Item) {list : α → List Item} {init : α → Acc}
    {singleStep : Item → Acc → WordOracleComp Operation Acc}
    (hlist : ComputableTidilyInPolyTime list input (encList encItem))
    (hinit : ComputableTidilyInPolyTime init input encAcc)
    (hstep : IsOraclePPTOn (encPair encItem encAcc) encAcc (fun p => singleStep p.1 p.2))
    {growth : ℕ}
    (hgrowth : ∀ x acc, ∀ next ∈ OracleComp.support (singleStep x acc),
      (encAcc next).length ≤ (encAcc acc).length + growth) :
    IsOraclePPTOn input encAcc (fun a => foldlMList singleStep (list a) (init a)) := by
  have hcount : ComputableTidilyInPolyTime (fun a => (list a).length) input encUnary :=
    (length (enc := encItem)).comp hlist
  have hinitial : ComputableTidilyInPolyTime (fun a => (list a, init a))
      input (encPair (encList encItem) encAcc) :=
    hlist.prod hinit
  have hprep : ComputableTidilyInPolyTime
      (fun st : List Item × Acc => (st.1.headD fallback, st.2))
      (encPair (encList encItem) encAcc) (encPair encItem encAcc) :=
    (listHeadDWithInput fallback (fst _ _)).prod (snd _ _)
  have htail : ComputableTidilyInPolyTime
      (fun st : List Item × Acc => st.1.tail)
      (encPair (encList encItem) encAcc) (encList encItem) :=
    (listTail encItem).comp (fst _ _)
  have hloopStep : IsOraclePPTOn (encPair (encList encItem) encAcc)
      (encPair (encList encItem) encAcc) (stepList fallback singleStep) :=
    (hstep.preprocess hprep).pair htail
  have hiter := IsOraclePPTOn.iterate_of_bounded_growth hcount hinitial hloopStep
    (growth := growth) fun ⟨L, acc⟩ next hnext => by
      obtain ⟨acc', hacc', rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      have h1 := length_encList_tail_le encItem L
      have h2 := hgrowth (L.headD fallback) acc acc' hacc'
      simp only [encPair_apply, List.length_append, length_frame]
      omega
  simpa only [iterate_stepList_eq_foldlMList] using
    hiter.map (snd (encList encItem) encAcc)

/-- Certify a monadic list fold `foldlMList singleStep (list a) (init a)` in `ProbComp`
from a constant growth bound on the accumulator encoding `encAcc`. -/
private theorem isPPTOn_foldlMList_of_bounded_growth
    {α Item Acc : Type}
    {input : α ↪ List Bool} {encItem : Item ↪ List Bool} {encAcc : Acc ↪ List Bool}
    (fallback : Item) {list : α → List Item} {init : α → Acc}
    {singleStep : Item → Acc → ProbComp Acc}
    (hlist : ComputableTidilyInPolyTime list input (encList encItem))
    (hinit : ComputableTidilyInPolyTime init input encAcc)
    (hstep : IsPPTOn (encPair encItem encAcc) encAcc (fun p => singleStep p.1 p.2))
    {growth : ℕ}
    (hgrowth : ∀ x acc, ∀ next ∈ (ProbComp.eval (singleStep x acc)).support,
      (encAcc next).length ≤ (encAcc acc).length + growth) :
    IsPPTOn input encAcc (fun a => foldlMList singleStep (list a) (init a)) := by
  have hcount : ComputableTidilyInPolyTime (fun a => (list a).length) input encUnary :=
    (length (enc := encItem)).comp hlist
  have hinitial : ComputableTidilyInPolyTime (fun a => (list a, init a))
      input (encPair (encList encItem) encAcc) :=
    hlist.prod hinit
  have hprep : ComputableTidilyInPolyTime
      (fun st : List Item × Acc => (st.1.headD fallback, st.2))
      (encPair (encList encItem) encAcc) (encPair encItem encAcc) :=
    (listHeadDWithInput fallback (fst _ _)).prod (snd _ _)
  have htail : ComputableTidilyInPolyTime
      (fun st : List Item × Acc => st.1.tail)
      (encPair (encList encItem) encAcc) (encList encItem) :=
    (listTail encItem).comp (fst _ _)
  have hloopStep : IsPPTOn (encPair (encList encItem) encAcc)
      (encPair (encList encItem) encAcc) (stepList fallback singleStep) :=
    (hstep.preprocess (.of_tidy hprep)).pair htail
  have hiter := IsPPTOn.iterate_of_bounded_growth hcount hinitial hloopStep
    (growth := growth) fun ⟨L, acc⟩ next hnext => by
      simp only [stepList, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
      obtain ⟨acc', hacc', rfl⟩ := hnext
      have h1 := length_encList_tail_le encItem L
      have h2 := hgrowth (L.headD fallback) acc acc' hacc'
      simp only [encPair_apply, List.length_append, length_frame]
      omega
  simpa only [iterate_stepList_eq_foldlMList] using
    hiter.map (.of_tidy (snd (encList encItem) encAcc))

/-- Private sampling in `ProbOracleComp` binds directly on `ProbComp.eval` without touching the
external oracle state `s`. -/
private theorem runWith_sample_bind {ι : Type} {spec : ι → Type} {α β State : Type}
    (oracle : (i : ι) → StateT State PMF (spec i))
    (d : ProbComp α) (k : α → ProbOracleComp spec β) (s : State) :
    ProbOracleComp.runWith oracle (ProbOracleComp.sample d >>= k) s =
      (ProbComp.eval d).bind (fun a => ProbOracleComp.runWith oracle (k a) s) := by
  simp [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    PMF.bind_map, Function.comp_def]

/-- Private coin draws `ProbOracleComp.sample d` commute with arbitrary stateful oracle
computations `m` under `ProbOracleComp.runWith`. -/
private theorem runWith_sample_comm {ι : Type} {spec : ι → Type} {α β γ State : Type}
    (oracle : (i : ι) → StateT State PMF (spec i))
    (d : ProbComp α) (m : ProbOracleComp spec β) (k : α → β → ProbOracleComp spec γ)
    (s : State) :
    ProbOracleComp.runWith oracle
      (ProbOracleComp.sample d >>= fun a => m >>= fun b => k a b) s =
    ProbOracleComp.runWith oracle
      (m >>= fun b => ProbOracleComp.sample d >>= fun a => k a b) s := by
  rw [runWith_sample_bind]
  conv_lhs => arg 2; ext a; rw [ProbOracleComp.runWith_bind]
  rw [PMF.bind_comm, ProbOracleComp.runWith_bind]
  congr 1
  funext b
  rw [← runWith_sample_bind]

/-- Replacing a private sample `d₁` with `f <$> d₂` when
`ProbComp.eval d₁ = (ProbComp.eval d₂).map f` preserves `ProbOracleComp.runWith` under every
stateful oracle. -/
private theorem runWith_sample_congr {ι : Type} {spec : ι → Type} {α β γ State : Type}
    (oracle : (i : ι) → StateT State PMF (spec i))
    (d₁ : ProbComp α) (d₂ : ProbComp β) (f : β → α)
    (heval : ProbComp.eval d₁ = (ProbComp.eval d₂).map f)
    (k : α → ProbOracleComp spec γ) (s : State) :
    ProbOracleComp.runWith oracle (ProbOracleComp.sample d₁ >>= k) s =
      ProbOracleComp.runWith oracle (ProbOracleComp.sample d₂ >>= fun b => k (f b)) s := by
  rw [runWith_sample_bind, runWith_sample_bind, heval, PMF.bind_map]
  rfl

/-! ### Section 4B: Word-Level Real and Simulated Runners and Their PPT Certificates -/

/-- Any family of distributions `fun a => g a <$> ProbComp.uniform (ι → Bool)` over a finite input
type `[Finite α]` and finite coin index type `[Fintype ι]` is strict PPT. -/
private theorem isPPTOn_of_finite_uniform {α β ι : Type} [Finite α] [Fintype ι] [DecidableEq ι]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (g : α → (ι → Bool) → β) :
    IsPPTOn input output (fun a => g a <$> ProbComp.uniform (ι → Bool)) := by
  cases nonempty_fintype α
  have hunif : IsPPTOn input (encFinite (ι → Bool)) (fun _ => ProbComp.uniform (ι → Bool)) :=
    isPPTOn_uniform_fintype_bool input (encFinite (ι → Bool))
  exact hunif.map_with (.of_tidy (of_finite (fun p : α × (ι → Bool) => g p.1 p.2)))

private theorem isPPTOn_sampleAdditiveShares (m : ℕ) :
    IsPPTOn encBool (encFinite (Fin m → Bool)) (ProbComp.sampleAdditiveShares m) :=
  isPPTOn_of_finite_uniform encBool (encFinite (Fin m → Bool)) (ProbComp.completeShares m)

/-- The `N`-bit additive share sent by party `s` to party `i` in Step 1 of `gmwCircuitProtocol`. -/
private def step1SenderShare (m N : ℕ) (xr_s c1_s : List Bool) (i : Fin m) : List Bool :=
  (List.range N).map fun j =>
    ProbComp.completeShares m (xr_s.getD j false)
      (Cslib.BitString.ofList (m - 1) (Cslib.BitString.listRow (m - 1) j c1_s)) i

/-- Initial input-wire list (and Step 1 received share transcript) of party `i` in
`gmwCircuitProtocol`. -/
private def step1Wires (m N : ℕ) (x_bits r_bits c1_bits : Fin m → List Bool) (i : Fin m) :
    List Bool :=
  (List.finRange m).flatMap fun s =>
    step1SenderShare m N (x_bits s ++ r_bits s) (c1_bits s) i

private theorem computableTidilyInPolyTime_step1Wires {α : Type} {input : α ↪ List Bool}
    (m : ℕ) {N : α → ℕ} {x_bits r_bits c1_bits : α → Fin m → List Bool}
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits)) :
    ComputableTidilyInPolyTime
      (fun a => step1Wires m (N a) (x_bits a) (r_bits a) (c1_bits a))
      input (encPi encBits) := by
  refine pi fun i => ?_
  have hsender (s : Fin m) :
      ComputableTidilyInPolyTime
        (fun a => step1SenderShare m (N a) (x_bits a s ++ r_bits a s) (c1_bits a s) i)
        input encBits := by
    have hxr : ComputableTidilyInPolyTime (fun a => x_bits a s ++ r_bits a s) input encBits :=
      bitsAppend ((pi_apply encBits s).comp hx) ((pi_apply encBits s).comp hr)
    have hc1s : ComputableTidilyInPolyTime (fun a => c1_bits a s) input encBits :=
      (pi_apply encBits s).comp hc1
    have hbit : ComputableTidilyInPolyTime
        (fun p : α × ℕ => (x_bits p.1 s ++ r_bits p.1 s).getD p.2 false)
        (encPair input encUnary) encBool :=
      bitsGetDWithInput (hxr.comp (fst _ _)) (snd _ _) false
    have hrow : ComputableTidilyInPolyTime
        (fun p : α × ℕ =>
          Cslib.BitString.ofList (m - 1) (Cslib.BitString.listRow (m - 1) p.2 (c1_bits p.1 s)))
        (encPair input encUnary) (encPi encBool) :=
      (computableTidilyInPolyTime_ofList_fin (m - 1)).comp
        (bitsRowWithInput (const (m - 1)) (snd _ _) (hc1s.comp (fst _ _)))
    have hcomp : ComputableTidilyInPolyTime
        (fun q : Bool × (Fin (m - 1) → Bool) => ProbComp.completeShares m q.1 q.2 i)
        (encPair encBool (encPi encBool)) encBool :=
      of_finite _
    exact mapToBitsWithInput (range.comp hN) (hcomp.comp (hbit.prod hrow))
  simpa only [step1Wires, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    bitsFlatten (mapConst (List.finRange m) fun s _ => hsender s)

/-- One pairwise $\text{OT}_1^4$ invocation in `twoPartyMulProtocol` at pair `p : OrderedPair m`
under `Steps.runEncoded`, returning `(c₀, ans_v) : Bool × Bool`. -/
private noncomputable def realPairCall (m : ℕ) (p : OrderedPair m) (x : Fin m → Bool × Bool) :
    WordOracleComp Unit (Bool × Bool) :=
  ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun c₀ =>
    (fun raw => (c₀, raw.headD false)) <$>
      List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encodeOT14Query
            (fun s => twoPartyMulQuery s (x (pairEmbedding p s), twoPartyMulCoins c₀ s)))

private theorem isOraclePPTOn_realPairCall (m : ℕ) (p : OrderedPair m) :
    IsOraclePPTOn (encFinite (Fin m → Bool × Bool)) (encPair encBool encBool)
      (realPairCall m p) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (Fin m → Bool × Bool))
    (tag := id) (branch := fun x _ => realPairCall m p x) id' ?_).congr
    fun _ _ _ _ => rfl
  intro x
  unfold realPairCall
  have hc₀ : IsOraclePPTOn (Operation := Unit) (encFinite (Fin m → Bool × Bool)) encBool
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) := by
    have hbool : IsPPTOn (encFinite (Fin m → Bool × Bool)) encBool
        (fun _ => ProbComp.uniform Bool) := by
      refine (isPPTOn_of_finite_uniform (encFinite (Fin m → Bool × Bool)) encBool
        (fun _ (f : Fin 1 → Bool) => f 0)).congr fun _ => ?_
      rw [ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_uniform]
      exact PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) Bool)
    exact hbool.isOraclePPTOn
  have hq : IsOraclePPTOn encBool encBits
      (fun c₀ : Bool =>
        List.take ((fun _ : Bool => 1) c₀) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encodeOT14Query
              (fun s => twoPartyMulQuery s (x (pairEmbedding p s), twoPartyMulCoins c₀ s)))) :=
    IsOraclePPTOn.query_take () (of_finite _) (const 1)
  have hpost : ComputableTidilyInPolyTime
      (fun q : Bool × List Bool => (q.1, q.2.headD false))
      (encPair encBool encBits) (encPair encBool encBool) :=
    (fst encBool encBits).prod
      (comp' (headD (encA := encBool) (encL := encBits) false) (snd encBool encBits))
  have hsecond := hq.map_with (f := fun c₀ raw => (c₀, raw.headD false)) hpost
  exact hc₀.bind hsecond

/-- Sequential execution of `realPairCall m p x` along `L : List (OrderedPair m)`. -/
private noncomputable def realPairsCalls (m : ℕ) (x : Fin m → Bool × Bool) :
    List (OrderedPair m) → WordOracleComp Unit (OrderedPair m → Bool × Bool)
  | [] => pure (fun _ => (false, false))
  | p :: L =>
    realPairCall m p x >>= fun res =>
      (fun rest => Function.update rest p res) <$> realPairsCalls m x L

private theorem isOraclePPTOn_realPairsCalls (m : ℕ) (L : List (OrderedPair m)) :
    IsOraclePPTOn (encFinite (Fin m → Bool × Bool)) (encFinite (OrderedPair m → Bool × Bool))
      (fun x => realPairsCalls m x L) := by
  induction L with
  | nil =>
    unfold realPairsCalls
    exact ((of_finite (fun _ : Fin m → Bool × Bool =>
      (fun _ : OrderedPair m => (false, false)))).isPPTOn).isOraclePPTOn
  | cons p L ih =>
    unfold realPairsCalls
    have hprep := ih.preprocess (fst (encFinite (Fin m → Bool × Bool)) (encPair encBool encBool))
    have hsecond := hprep.map_with
      (f := fun pair rest => Function.update rest p pair.2)
      (of_finite (encB := encFinite (OrderedPair m → Bool × Bool)) _)
    exact (isOraclePPTOn_realPairCall m p).bind_with
      (second := fun x res =>
        (fun rest => Function.update rest p res) <$> realPairsCalls m x L)
      hsecond

private theorem length_flatten_ite_singleton_le {α : Type} (L : List α)
    (P : α → Prop) [DecidablePred P] (f : α → Bool) :
    ((L.map fun a => if P a then [f a] else []).flatten).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.flatten_cons]
    split_ifs <;> (simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- Deterministic extraction of `(ans, ot_c_delta, ot_a_delta)` from one `multiPartyMulProtocol m`
invocation given the pair transcript `tr : OrderedPair m → Bool × Bool`. -/
private def realSharedMulPure (m : ℕ) (x : Fin m → Bool × Bool) (tr : OrderedPair m → Bool × Bool) :
    (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool) :=
  (fun i =>
    m • ((x i).1 * (x i).2) +
      ((orderedPairs m).map fun p =>
        if p.1.1 = i then (tr p).1 else if p.1.2 = i then (tr p).2 else 0).sum,
   fun i => ((orderedPairs m).map fun p => if p.1.1 = i then [(tr p).1] else []).flatten,
   fun i => ((orderedPairs m).map fun p => if p.1.2 = i then [(tr p).2] else []).flatten)

/-- Deterministic extraction of `(ot_c_delta, ot_a_delta)` from one simulated `multiPartyMulSim m I`
invocation composed with `twoPartyMulSim`. -/
private def simSharedMulPure (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (x : Fin m → Bool × Bool) (ans : Fin m → Bool) (r : OrderedPair m → Bool) :
    (Fin m → List Bool) × (Fin m → List Bool) :=
  let x₀ := MultiPartyMul.extendIn I (I.restrict x)
  let y₀ := MultiPartyMul.extendOut I (I.restrict ans)
  let rSim := MultiPartyMul.tildeR (MultiPartyMul.pivotParty I) x₀ y₀ r
  (fun i =>
    ((orderedPairs m).map fun p =>
      if p.1.1 = i then [MultiPartyMul.matrixOfCoins x₀ rSim i p.1.2] else []).flatten,
   fun i =>
    ((orderedPairs m).map fun p =>
      if p.1.2 = i then [MultiPartyMul.matrixOfCoins x₀ rSim i p.1.1] else []).flatten)

/-- Step 2 accumulator `(wires, ot_coins, ot_ans)`. -/
private abbrev Step2Acc (m : ℕ) : Type :=
  (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool)

/-- Encoding of `Step2Acc m`. -/
private noncomputable def encStep2Acc (m : ℕ) : Step2Acc m ↪ List Bool :=
  encPair (encPi encBits) (encPair (encPi encBits) (encPi encBits))

/-- Append per-party Step 2 deltas `(w_delta, ot_c_delta, ot_a_delta)` to `acc : Step2Acc m`. -/
private def appendStep2Acc (m : ℕ) (acc delta : Step2Acc m) : Step2Acc m :=
  (fun i => acc.1 i ++ delta.1 i,
   fun i => acc.2.1 i ++ delta.2.1 i,
   fun i => acc.2.2 i ++ delta.2.2 i)

private theorem computableTidilyInPolyTime_appendPiBits (m : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : (Fin m → List Bool) × (Fin m → List Bool) => fun i => p.1 i ++ p.2 i)
      (encPair (encPi encBits) (encPi encBits)) (encPi encBits) :=
  pi fun i =>
    bitsAppend
      ((pi_apply encBits i).comp (fst (encPi encBits) (encPi encBits)))
      ((pi_apply encBits i).comp (snd (encPi encBits) (encPi encBits)))

private theorem computableTidilyInPolyTime_appendStep2Acc (m : ℕ) :
    ComputableTidilyInPolyTime (fun p : Step2Acc m × Step2Acc m => appendStep2Acc m p.1 p.2)
      (encPair (encStep2Acc m) (encStep2Acc m)) (encStep2Acc m) := by
  let e := encPi (Index := Fin m) encBits
  let e2 := encPair e e
  let e3 := encStep2Acc m
  have h1 := (computableTidilyInPolyTime_appendPiBits m).comp
    (((fst e e2).comp (fst e3 e3)).prod ((fst e e2).comp (snd e3 e3)))
  have h2 := (computableTidilyInPolyTime_appendPiBits m).comp
    ((((fst e e).comp (snd e e2)).comp (fst e3 e3)).prod
      (((fst e e).comp (snd e e2)).comp (snd e3 e3)))
  have h3 := (computableTidilyInPolyTime_appendPiBits m).comp
    ((((snd e e).comp (snd e e2)).comp (fst e3 e3)).prod
      (((snd e e).comp (snd e e2)).comp (snd e3 e3)))
  exact h1.prod (h2.prod h3)

private theorem length_encStep2Acc_appendStep2Acc_le (m : ℕ) (acc delta : Step2Acc m)
    (hw : ∀ i, (delta.1 i).length ≤ 1)
    (hc : ∀ i, (delta.2.1 i).length ≤ (orderedPairs m).length)
    (ha : ∀ i, (delta.2.2 i).length ≤ (orderedPairs m).length) :
    (encStep2Acc m (appendStep2Acc m acc delta)).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  have h1 := length_encPi_encBits_le acc.1 (fun i => acc.1 i ++ delta.1 i) 1
    (fun i => by simp [hw i])
  have h2 := length_encPi_encBits_le acc.2.1 (fun i => acc.2.1 i ++ delta.2.1 i)
    (orderedPairs m).length (fun i => by simp [hc i])
  have h3 := length_encPi_encBits_le acc.2.2 (fun i => acc.2.2 i ++ delta.2.2 i)
    (orderedPairs m).length (fun i => by simp [ha i])
  have hr : m * (4 + 6 * (orderedPairs m).length) =
      2 * (m * (2 * 1)) + 2 * (m * (2 * (orderedPairs m).length)) +
        m * (2 * (orderedPairs m).length) := by
    ring
  simp only [encStep2Acc, appendStep2Acc, encPair_apply, List.length_append, length_frame, hr]
  omega

/-- Extract `(op, x)` from `(gate, acc)` for Step 2 gate evaluation. -/
private def extractGateCoreInput (m : ℕ) (st : (Boolean.Op × List ℕ) × Step2Acc m) :
    Boolean.Op × (Fin m → Bool × Bool) :=
  (st.1.1, fun s =>
    ((st.2.1 s).getD (st.1.2.getD 0 0) false,
     (st.2.1 s).getD (st.1.2.getD 1 0) false))

private theorem computableTidilyInPolyTime_extractGateCoreInput (m : ℕ) :
    ComputableTidilyInPolyTime (extractGateCoreInput m)
      (encPair Boolean.encGate (encStep2Acc m))
      (encFinite (Boolean.Op × (Fin m → Bool × Bool))) := by
  let eGate := Boolean.encGate
  let eAcc := encStep2Acc m
  let ePi := encPi (Index := Fin m) encBits
  have hop : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => st.1.1)
      (encPair eGate eAcc) Boolean.encOp :=
    (fst Boolean.encOp (encList encNat)).comp (fst eGate eAcc)
  have hwiresList : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => st.1.2)
      (encPair eGate eAcc) (encList encNat) :=
    (snd Boolean.encOp (encList encNat)).comp (fst eGate eAcc)
  have hidx0 : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => st.1.2.getD 0 0)
      (encPair eGate eAcc) encNat :=
    (listGetD (encA := encNat) 0).comp (hwiresList.prod (const 0))
  have hidx1 : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => st.1.2.getD 1 0)
      (encPair eGate eAcc) encNat :=
    (listGetD (encA := encNat) 0).comp (hwiresList.prod (const 1))
  have hx : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => fun s : Fin m =>
        ((st.2.1 s).getD (st.1.2.getD 0 0) false,
         (st.2.1 s).getD (st.1.2.getD 1 0) false))
      (encPair eGate eAcc) (encPi (encPair encBool encBool)) := by
    refine pi fun s => ?_
    have hws := (pi_apply encBits s).comp ((fst ePi (encPair ePi ePi)).comp (snd eGate eAcc))
    exact (listGetD_binary (encA := encBool) false hws hidx0).prod
      (listGetD_binary (encA := encBool) false hws hidx1)
  exact (of_finite (encA := encPair Boolean.encOp (encPi (encPair encBool encBool))) id).comp
    (hop.prod hx)

/-- Format the per-party Step 2 deltas `(w_delta, ot_c_delta, ot_a_delta)` for an `.and`
(`isOr = false`) or `.or` (`isOr = true`) gate. -/
private def finishMulGate (m : ℕ) (isOr : Bool) (x : Fin m → Bool × Bool)
    (res : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
    Step2Acc m :=
  (fun i => [if isOr then (x i).1 + (x i).2 + res.1 i else res.1 i],
   res.2.1, res.2.2)

/-- Finite-input core of one real Step 2 gate evaluation. -/
private noncomputable def realGateCore (m : ℕ) [NeZero m] (p : Boolean.Op × (Fin m → Bool × Bool)) :
    WordOracleComp Unit (Step2Acc m) :=
  match p.1 with
  | .const b =>
    pure (fun i => [GMWCircuit.constShare b i], fun _ => [], fun _ => [])
  | .not =>
    pure (fun i => [(p.2 i).1 + GMWCircuit.constShare true i], fun _ => [], fun _ => [])
  | .and =>
    (fun tr => finishMulGate m false p.2 (realSharedMulPure m p.2 tr)) <$>
      realPairsCalls m p.2 (orderedPairs m)
  | .or =>
    (fun tr => finishMulGate m true p.2 (realSharedMulPure m p.2 tr)) <$>
      realPairsCalls m p.2 (orderedPairs m)

private theorem isOraclePPTOn_realGateCore (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool))) (encStep2Acc m)
      (realGateCore m) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (Boolean.Op × (Fin m → Bool × Bool)))
    (tag := id) (branch := fun choice _ => realGateCore m choice) id' ?_).congr
    fun _ _ _ _ => rfl
  rintro ⟨op, x⟩
  cases op with
  | const b =>
    exact ((of_finite _).isPPTOn).isOraclePPTOn
  | not =>
    exact ((of_finite _).isPPTOn).isOraclePPTOn
  | and =>
    exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess (const x)).map
      (of_finite (fun tr => finishMulGate m false x (realSharedMulPure m x tr))))
  | or =>
    exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess (const x)).map
      (of_finite (fun tr => finishMulGate m true x (realSharedMulPure m x tr))))

/-- Finite-input core of one simulated Step 2 gate evaluation. -/
private noncomputable def simGateCore (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (p : Boolean.Op × (Fin m → Bool × Bool)) :
    ProbComp (Step2Acc m) :=
  match p.1 with
  | .const b =>
    pure (fun i => [GMWCircuit.constShare b i], fun _ => [], fun _ => [])
  | .not =>
    pure (fun i => [(p.2 i).1 + GMWCircuit.constShare true i], fun _ => [], fun _ => [])
  | .and => do
    let ans ← ProbComp.sampleAdditiveShares m ((∑ i : Fin m, (p.2 i).1) * (∑ i : Fin m, (p.2 i).2))
    let r ← ProbComp.uniform (OrderedPair m → Bool)
    return finishMulGate m false p.2 (ans, simSharedMulPure m I p.2 ans r)
  | .or => do
    let ans ← ProbComp.sampleAdditiveShares m ((∑ i : Fin m, (p.2 i).1) * (∑ i : Fin m, (p.2 i).2))
    let r ← ProbComp.uniform (OrderedPair m → Bool)
    return finishMulGate m true p.2 (ans, simSharedMulPure m I p.2 ans r)

private theorem isPPTOn_simGateCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool))) (encStep2Acc m)
      (simGateCore m I) := by
  have hmul (isOr : Bool) (x : Fin m → Bool × Bool) :
      IsPPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool))) (encStep2Acc m)
        (fun _ => do
          let ans ← ProbComp.sampleAdditiveShares m
            ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2))
          let r ← ProbComp.uniform (OrderedPair m → Bool)
          return finishMulGate m isOr x (ans, simSharedMulPure m I x ans r)) := by
    have hans : IsPPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool)))
        (encFinite (Fin m → Bool))
        (fun _ => ProbComp.sampleAdditiveShares m
          ((∑ i : Fin m, (x i).1) * (∑ i : Fin m, (x i).2))) :=
      (isPPTOn_sampleAdditiveShares m).preprocess (.of_tidy (const _))
    have hot : IsPPTOn (encFinite (Fin m → Bool)) (encStep2Acc m)
        (fun ans => do
          let r ← ProbComp.uniform (OrderedPair m → Bool)
          return finishMulGate m isOr x (ans, simSharedMulPure m I x ans r)) := by
      refine (isPPTOn_of_finite_uniform (encFinite (Fin m → Bool)) (encStep2Acc m)
        (fun ans r => finishMulGate m isOr x (ans, simSharedMulPure m I x ans r))).congr
        fun _ => rfl
    exact hans.bind hot
  refine (IsPPTOn.finite_cases
    (tagEncoding := encFinite (Boolean.Op × (Fin m → Bool × Bool)))
    (tag := id) (branch := fun choice _ => simGateCore m I choice) id' ?_).congr
    fun _ => rfl
  rintro ⟨op, x⟩
  cases op with
  | const b => exact (of_finite _).isPPTOn
  | not => exact (of_finite _).isPPTOn
  | and => exact hmul false x
  | or => exact hmul true x

/-- Single Step 2 gate transition in `realRunWord`. -/
private noncomputable def realGateStep (m : ℕ) [NeZero m] (gate : Boolean.Op × List ℕ)
    (acc : Step2Acc m) :
    WordOracleComp Unit (Step2Acc m) :=
  appendStep2Acc m acc <$> realGateCore m (extractGateCoreInput m (gate, acc))

private theorem isOraclePPTOn_realGateStep (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encPair Boolean.encGate (encStep2Acc m)) (encStep2Acc m)
      (fun p => realGateStep m p.1 p.2) := by
  let eGate := Boolean.encGate
  let eAcc := encStep2Acc m
  let eIn := encPair eGate eAcc
  have hpost :=
    comp' (computableTidilyInPolyTime_appendStep2Acc m)
      ((comp' (snd eGate eAcc) (fst eIn eAcc)).prod (snd eIn eAcc))
  dsimp only at hpost
  have hprep := (isOraclePPTOn_realGateCore m).preprocess
    (computableTidilyInPolyTime_extractGateCoreInput m)
  exact hprep.map_with (f := fun p delta => appendStep2Acc m p.2 delta) hpost

private theorem realGateStep_growth (m : ℕ) [NeZero m]
    (gate : Boolean.Op × List ℕ) (acc next : Step2Acc m)
    (hnext : next ∈ OracleComp.support (realGateStep m gate acc)) :
    (encStep2Acc m next).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  obtain ⟨delta, hdelta, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  refine length_encStep2Acc_appendStep2Acc_le m acc delta ?_ ?_ ?_
  all_goals
    intro i
    rcases hg : extractGateCoreInput m (gate, acc) with ⟨op, x⟩
    rw [hg] at hdelta
    cases op with
    | const b =>
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hdelta
      simp
    | not =>
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hdelta
      simp
    | and =>
      simp only [realGateCore] at hdelta
      obtain ⟨tr, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hdelta
      dsimp only [finishMulGate, realSharedMulPure]
      first | (simp; done) | exact length_flatten_ite_singleton_le _ _ _
    | or =>
      simp only [realGateCore] at hdelta
      obtain ⟨tr, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hdelta
      dsimp only [finishMulGate, realSharedMulPure]
      first | (simp; done) | exact length_flatten_ite_singleton_le _ _ _

/-- Single Step 2 gate transition in `simRunWord`. -/
private noncomputable def simGateStep (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ) (acc : Step2Acc m) :
    ProbComp (Step2Acc m) :=
  appendStep2Acc m acc <$> simGateCore m I (extractGateCoreInput m (gate, acc))

private theorem isPPTOn_simGateStep (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encPair Boolean.encGate (encStep2Acc m)) (encStep2Acc m)
      (fun p => simGateStep m I p.1 p.2) := by
  let eGate := Boolean.encGate
  let eAcc := encStep2Acc m
  let eIn := encPair eGate eAcc
  have hpost :=
    comp' (computableTidilyInPolyTime_appendStep2Acc m)
      ((comp' (snd eGate eAcc) (fst eIn eAcc)).prod (snd eIn eAcc))
  dsimp only at hpost
  have hprep := (isPPTOn_simGateCore m I).preprocess
    (ComputableInPolyTime.of_tidy (computableTidilyInPolyTime_extractGateCoreInput m))
  exact hprep.map_with
    (f := fun p delta => appendStep2Acc m p.2 delta) (ComputableInPolyTime.of_tidy hpost)

private theorem simGateStep_growth (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ) (acc next : Step2Acc m)
    (hnext : next ∈ (ProbComp.eval (simGateStep m I gate acc)).support) :
    (encStep2Acc m next).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  simp only [simGateStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨delta, hdelta, rfl⟩ := hnext
  refine length_encStep2Acc_appendStep2Acc_le m acc delta ?_ ?_ ?_
  all_goals
    intro i
    rcases hg : extractGateCoreInput m (gate, acc) with ⟨op, x⟩
    rw [hg] at hdelta
    cases op with
    | const b =>
      simp only [simGateCore, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdelta
      subst hdelta; simp
    | not =>
      simp only [simGateCore, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdelta
      subst hdelta; simp
    | and =>
      simp only [simGateCore, ProbComp.eval_bind, ProbComp.eval_map,
        bind_pure_comp, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hdelta
      obtain ⟨ans, _, r, _, rfl⟩ := hdelta
      dsimp only [finishMulGate, simSharedMulPure]
      first | (simp; done) | exact length_flatten_ite_singleton_le _ _ _
    | or =>
      simp only [simGateCore, ProbComp.eval_bind, ProbComp.eval_map,
        bind_pure_comp, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hdelta
      obtain ⟨ans, _, r, _, rfl⟩ := hdelta
      dsimp only [finishMulGate, simSharedMulPure]
      first | (simp; done) | exact length_flatten_ite_singleton_le _ _ _

/-- Step 3 item `(r_party, a_shares, y_bit)` for output coordinate `(r_party, j)`. -/
private abbrev OutItem (m : ℕ) : Type :=
  Fin m × (Fin m → Bool) × Bool

/-- Step 3 accumulator `(ot_coins, ot_ans, out_msgs, y_out)`. -/
private abbrev Step3Acc (m : ℕ) : Type :=
  (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool)

/-- Encoding of `Step3Acc m`. -/
private noncomputable def encStep3Acc (m : ℕ) : Step3Acc m ↪ List Bool :=
  encPair (encPi encBits) (encPair (encPi encBits) (encPair (encPi encBits) (encPi encBits)))

/-- Append per-party Step 3 deltas `(ot_c_delta, ot_a_delta, msg_delta, y_delta)` to `acc`. -/
private def appendStep3Acc (m : ℕ) (acc delta : Step3Acc m) : Step3Acc m :=
  (fun i => acc.1 i ++ delta.1 i,
   fun i => acc.2.1 i ++ delta.2.1 i,
   fun i => acc.2.2.1 i ++ delta.2.2.1 i,
   fun i => acc.2.2.2 i ++ delta.2.2.2 i)

private theorem computableTidilyInPolyTime_appendStep3Acc (m : ℕ) :
    ComputableTidilyInPolyTime (fun p : Step3Acc m × Step3Acc m => appendStep3Acc m p.1 p.2)
      (encPair (encStep3Acc m) (encStep3Acc m)) (encStep3Acc m) := by
  let e := encPi (Index := Fin m) encBits
  let e2 := encStep2Acc m
  let e3 := encStep3Acc m
  have h1 := (computableTidilyInPolyTime_appendPiBits m).comp
    (((fst e e2).comp (fst e3 e3)).prod ((fst e e2).comp (snd e3 e3)))
  have h234 := (computableTidilyInPolyTime_appendStep2Acc m).comp
    (((snd e e2).comp (fst e3 e3)).prod ((snd e e2).comp (snd e3 e3)))
  exact h1.prod h234

private theorem length_encStep3Acc_appendStep3Acc_le (m : ℕ) (acc delta : Step3Acc m)
    (hc : ∀ i, (delta.1 i).length ≤ (orderedPairs m).length)
    (ha : ∀ i, (delta.2.1 i).length ≤ (orderedPairs m).length)
    (hm : ∀ i, (delta.2.2.1 i).length ≤ m)
    (hy : ∀ i, (delta.2.2.2 i).length ≤ 1) :
    (encStep3Acc m (appendStep3Acc m acc delta)).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  have h1 := length_encPi_encBits_le acc.1 (fun i => acc.1 i ++ delta.1 i)
    (orderedPairs m).length (fun i => by simp [hc i])
  have h2 := length_encPi_encBits_le acc.2.1 (fun i => acc.2.1 i ++ delta.2.1 i)
    (orderedPairs m).length (fun i => by simp [ha i])
  have h3 := length_encPi_encBits_le acc.2.2.1 (fun i => acc.2.2.1 i ++ delta.2.2.1 i)
    m (fun i => by simp [hm i])
  have h4 := length_encPi_encBits_le acc.2.2.2 (fun i => acc.2.2.2 i ++ delta.2.2.2 i)
    1 (fun i => by simp [hy i])
  have hr : m * (2 + 4 * m + 8 * (orderedPairs m).length) =
      2 * (m * (2 * (orderedPairs m).length)) +
        2 * (m * (2 * (orderedPairs m).length)) +
        2 * (m * (2 * m)) +
        m * (2 * 1) := by
    ring
  simp only [encStep3Acc, appendStep3Acc, encPair_apply, List.length_append, length_frame, hr]
  omega

/-- Build the list of `m * k` Step 3 items `(r_party, a_shares, y_bit)` from the designated output
wire indices `outputs : List ℕ`, final wire lists `wires : Fin m → List Bool`, and target output
bits `y_bits : Fin m → List Bool`. -/
private def buildOutItems (m k : ℕ) (I : Finset (Fin m))
    (outputs : List ℕ) (wires y_bits : Fin m → List Bool) :
    List (OutItem m) :=
  (List.finRange m).flatMap fun r =>
    (List.range k).map fun j =>
      let wIdx := outputs.getD (r.val * k + j) 0
      (r,
       fun s => (wires s).getD wIdx false,
       if r ∈ I then (y_bits r).getD j false else false)

private theorem computableTidilyInPolyTime_buildOutItems {α : Type} {input : α ↪ List Bool}
    (m : ℕ) (I : Finset (Fin m)) {k : α → ℕ}
    {outputs : α → List ℕ} {wires y_bits : α → Fin m → List Bool}
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (houtputs : ComputableTidilyInPolyTime outputs input (encList encNat))
    (hwires : ComputableTidilyInPolyTime wires input (encPi encBits))
    (hy : ComputableTidilyInPolyTime y_bits input (encPi encBits)) :
    ComputableTidilyInPolyTime
      (fun a => buildOutItems m (k a) I (outputs a) (wires a) (y_bits a))
      input (encList (encFinite (OutItem m))) := by
  refine flatMapConst (List.finRange m) fun r _ => ?_
  have hkBin : ComputableTidilyInPolyTime (fun p : α × ℕ => k p.1)
      (encPair input encUnary) encNat :=
    unary_to_binary.comp (hk.comp (fst input encUnary))
  have hjBin : ComputableTidilyInPolyTime (fun p : α × ℕ => p.2)
      (encPair input encUnary) encNat :=
    unary_to_binary.comp (snd input encUnary)
  have hidx : ComputableTidilyInPolyTime
      (fun p : α × ℕ => r.val * k p.1 + p.2)
      (encPair input encUnary) encNat := by
    fun_prop
  have hwIdx : ComputableTidilyInPolyTime
      (fun p : α × ℕ => (outputs p.1).getD (r.val * k p.1 + p.2) 0)
      (encPair input encUnary) encNat :=
    listGetD_binary (encA := encNat) 0 (houtputs.comp (fst input encUnary)) hidx
  have ha_shares : ComputableTidilyInPolyTime
      (fun p : α × ℕ => fun s : Fin m =>
        ((wires p.1) s).getD ((outputs p.1).getD (r.val * k p.1 + p.2) 0) false)
      (encPair input encUnary) (encPi encBool) := by
    refine pi fun s => ?_
    exact listGetD_binary (encA := encBool) false
      (((pi_apply encBits s).comp hwires).comp (fst input encUnary)) hwIdx
  have hy_bit : ComputableTidilyInPolyTime
      (fun p : α × ℕ => if r ∈ I then (y_bits p.1 r).getD p.2 false else false)
      (encPair input encUnary) encBool := by
    by_cases hr : r ∈ I
    · simpa only [hr, ↓reduceIte, Function.comp_def] using
        bitsGetDWithInput (((pi_apply encBits r).comp hy).comp (fst input encUnary))
          (snd input encUnary) false
    · simpa only [hr, ↓reduceIte] using const false
  have hpack : ComputableTidilyInPolyTime
      (fun q : (Fin m → Bool) × Bool => (r, q.1, q.2))
      (encPair (encPi encBool) encBool) (encFinite (OutItem m)) :=
    of_finite _
  exact mapWithInput (range.comp hk) (hpack.comp (ha_shares.prod hy_bit))

/-- Format the per-party Step 3 deltas `(ot_c_delta, ot_a_delta, msg_delta, y_delta)` for recipient
`r_party : Fin m`. -/
private def finishOutStep (m : ℕ) (r_party : Fin m)
    (res : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
    Step3Acc m :=
  (res.2.1,
   res.2.2,
   fun i => if i = r_party then List.ofFn res.1 else [],
   fun i => if i = r_party then [∑ s : Fin m, res.1 s] else [])

/-- Finite-input core of one real Step 3 output-coordinate refresh and reconstruction. -/
private noncomputable def realOutCore (m : ℕ) [NeZero m] (item : OutItem m) :
    WordOracleComp Unit (Step3Acc m) :=
  (fun tr =>
    finishOutStep m item.1
      (realSharedMulPure m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) tr)) <$>
    realPairsCalls m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) (orderedPairs m)

private theorem isOraclePPTOn_realOutCore (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encFinite (OutItem m)) (encStep3Acc m) (realOutCore m) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (OutItem m))
    (tag := id) (branch := fun item _ => realOutCore m item) id' ?_).congr
    fun _ _ _ _ => rfl
  intro item
  exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess
    (const (fun s => (item.2.1 s, GMWCircuit.constShare true s)))).map
    (of_finite (fun tr =>
      finishOutStep m item.1
        (realSharedMulPure m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) tr))))

/-- Finite-input core of one simulated Step 3 output-coordinate refresh and reconstruction. -/
private noncomputable def simOutCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) (item : OutItem m) :
    ProbComp (Step3Acc m) := do
  let ans ← ProbComp.sampleAdditiveShares m item.2.2
  let r ← ProbComp.uniform (OrderedPair m → Bool)
  return finishOutStep m item.1
    (ans, simSharedMulPure m I (fun s => (item.2.1 s, GMWCircuit.constShare true s)) ans r)

private theorem isPPTOn_simOutCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encFinite (OutItem m)) (encStep3Acc m) (simOutCore m I) := by
  refine (IsPPTOn.finite_cases
    (tagEncoding := encFinite (OutItem m))
    (tag := id) (branch := fun item _ => simOutCore m I item) id' ?_).congr
    fun _ => rfl
  intro item
  have hans : IsPPTOn (encFinite (OutItem m)) (encFinite (Fin m → Bool))
      (fun _ => ProbComp.sampleAdditiveShares m item.2.2) :=
    (isPPTOn_sampleAdditiveShares m).preprocess (.of_tidy (const item.2.2))
  have hot : IsPPTOn (encFinite (Fin m → Bool)) (encStep3Acc m)
      (fun ans => do
        let r ← ProbComp.uniform (OrderedPair m → Bool)
        return finishOutStep m item.1
          (ans,
           simSharedMulPure m I (fun s => (item.2.1 s, GMWCircuit.constShare true s)) ans r)) := by
    refine (isPPTOn_of_finite_uniform (encFinite (Fin m → Bool)) (encStep3Acc m)
      (fun ans r =>
        finishOutStep m item.1
          (ans,
           simSharedMulPure m I
             (fun s => (item.2.1 s, GMWCircuit.constShare true s)) ans r))).congr
      fun _ => rfl
  exact hans.bind hot

/-- Single Step 3 output-coordinate transition in `realRunWord`. -/
private noncomputable def realOutStep (m : ℕ) [NeZero m] (item : OutItem m) (acc : Step3Acc m) :
    WordOracleComp Unit (Step3Acc m) :=
  appendStep3Acc m acc <$> realOutCore m item

private theorem isOraclePPTOn_realOutStep (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encPair (encFinite (OutItem m)) (encStep3Acc m)) (encStep3Acc m)
      (fun p => realOutStep m p.1 p.2) := by
  let eItem := encFinite (OutItem m)
  let eAcc := encStep3Acc m
  let eIn := encPair eItem eAcc
  have hpost :=
    comp' (computableTidilyInPolyTime_appendStep3Acc m)
      ((comp' (snd eItem eAcc) (fst eIn eAcc)).prod (snd eIn eAcc))
  dsimp only at hpost
  have hprep := (isOraclePPTOn_realOutCore m).preprocess (fst eItem eAcc)
  exact hprep.map_with (f := fun p delta => appendStep3Acc m p.2 delta) hpost

private theorem realOutStep_growth (m : ℕ) [NeZero m]
    (item : OutItem m) (acc next : Step3Acc m)
    (hnext : next ∈ OracleComp.support (realOutStep m item acc)) :
    (encStep3Acc m next).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  obtain ⟨delta, hdelta, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simp only [realOutCore] at hdelta
  obtain ⟨tr, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hdelta
  refine length_encStep3Acc_appendStep3Acc_le m acc _ ?_ ?_ ?_ ?_
  · intro i
    dsimp only [finishOutStep, realSharedMulPure]
    exact length_flatten_ite_singleton_le _ _ _
  · intro i
    dsimp only [finishOutStep, realSharedMulPure]
    exact length_flatten_ite_singleton_le _ _ _
  · intro i; dsimp only [finishOutStep]; split_ifs <;> simp
  · intro i; dsimp only [finishOutStep]; split_ifs <;> simp

/-- Single Step 3 output-coordinate transition in `simRunWord`. -/
private noncomputable def simOutStep (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (item : OutItem m) (acc : Step3Acc m) :
    ProbComp (Step3Acc m) :=
  appendStep3Acc m acc <$> simOutCore m I item

private theorem isPPTOn_simOutStep (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encPair (encFinite (OutItem m)) (encStep3Acc m)) (encStep3Acc m)
      (fun p => simOutStep m I p.1 p.2) := by
  unfold simOutStep
  let eItem := encFinite (OutItem m)
  let eAcc := encStep3Acc m
  let eIn := encPair eItem eAcc
  have hpost :=
    comp' (computableTidilyInPolyTime_appendStep3Acc m)
      ((comp' (snd eItem eAcc) (fst eIn eAcc)).prod (snd eIn eAcc))
  dsimp only at hpost
  have hprep := (isPPTOn_simOutCore m I).preprocess (ComputableInPolyTime.of_tidy (fst eItem eAcc))
  have hres := hprep.map_with
    (f := fun p delta => appendStep3Acc m p.2 delta) (ComputableInPolyTime.of_tidy hpost)
  exact hres

private theorem simOutStep_growth (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (item : OutItem m) (acc next : Step3Acc m)
    (hnext : next ∈ (ProbComp.eval (simOutStep m I item acc)).support) :
    (encStep3Acc m next).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  simp only [simOutStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨delta, hdelta, rfl⟩ := hnext
  simp only [simOutCore, ProbComp.eval_bind, ProbComp.eval_map,
    bind_pure_comp, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hdelta
  obtain ⟨ans, _, r, _, rfl⟩ := hdelta
  refine length_encStep3Acc_appendStep3Acc_le m acc _ ?_ ?_ ?_ ?_
  · intro i
    dsimp only [finishOutStep, simSharedMulPure]
    exact length_flatten_ite_singleton_le _ _ _
  · intro i
    dsimp only [finishOutStep, simSharedMulPure]
    exact length_flatten_ite_singleton_le _ _ _
  · intro i; dsimp only [finishOutStep]; split_ifs <;> simp
  · intro i; dsimp only [finishOutStep]; split_ifs <;> simp

/-- Assemble party `i`'s 7-tuple view word from its 7 `List Bool` components, matching
`encGMWPartyView`. -/
private def packPartyViewWord {m : ℕ}
    (x_bits r_bits c1_bits ot_coins in_shares ot_ans out_msgs : Fin m → List Bool)
    (i : Fin m) : List Bool :=
  encPair
    (encPair (encPair encBits encBits) (encPair encBits encBits))
    (encPair encBits (encPair encBits encBits))
    (((x_bits i, r_bits i), (c1_bits i, ot_coins i)),
     (in_shares i, (ot_ans i, out_msgs i)))

/-- Assemble the final `List Bool` output of `Protocol.runEncoded` from all 8 `Fin m → List Bool`
components `(x_bits, r_bits, c1_bits, in_shares)` and
`acc3 = (ot_coins, ot_ans, out_msgs, y_out)`. -/
private def packRealOutput (m : ℕ)
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (acc3 : Step3Acc m) : List Bool :=
  encPair (encList encBits) (encList encBits)
    ((List.finRange m).map
       (packPartyViewWord x_bits r_bits c1_bits acc3.1 in_shares acc3.2.1 acc3.2.2.1),
     (List.finRange m).map acc3.2.2.2)

/-- Assemble the final `List Bool` output of `encodeCoalitionView` from `(x_bits, r_bits, c1_bits,
in_shares)` and `acc3 = (ot_coins, ot_ans, out_msgs, y_out)`. -/
private def packSimOutput (m : ℕ) (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (acc3 : Step3Acc m) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i =>
      if i ∈ I then
        packPartyViewWord x_bits r_bits c1_bits acc3.1 in_shares acc3.2.1 acc3.2.2.1 i
      else [])

private theorem computableTidilyInPolyTime_packPartyViewWord {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {x_bits r_bits c1_bits ot_coins in_shares ot_ans out_msgs : α → Fin m → List Bool}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hot_c : ComputableTidilyInPolyTime ot_coins input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hot_a : ComputableTidilyInPolyTime ot_ans input (encPi encBits))
    (hout_m : ComputableTidilyInPolyTime out_msgs input (encPi encBits))
    (i : Fin m) :
    ComputableTidilyInPolyTime
      (fun a => packPartyViewWord (x_bits a) (r_bits a) (c1_bits a) (ot_coins a)
        (in_shares a) (ot_ans a) (out_msgs a) i)
      input encBits := by
  have htuple : ComputableTidilyInPolyTime
      (fun a =>
        (((x_bits a i, r_bits a i), (c1_bits a i, ot_coins a i)),
         (in_shares a i, (ot_ans a i, out_msgs a i))))
      input
      (encPair
        (encPair (encPair encBits encBits) (encPair encBits encBits))
        (encPair encBits (encPair encBits encBits))) :=
    ((((comp' (pi_apply encBits i) hx).prod (comp' (pi_apply encBits i) hr)).prod
      ((comp' (pi_apply encBits i) hc1).prod (comp' (pi_apply encBits i) hot_c))).prod
      ((comp' (pi_apply encBits i) hin).prod
        ((comp' (pi_apply encBits i) hot_a).prod (comp' (pi_apply encBits i) hout_m))))
  exact htuple.encoded

private theorem computableTidilyInPolyTime_packRealOutput {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {x_bits r_bits c1_bits in_shares : α → Fin m → List Bool}
    {acc3 : α → Step3Acc m}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hacc3 : ComputableTidilyInPolyTime acc3 input (encStep3Acc m)) :
    ComputableTidilyInPolyTime
      (fun a => packRealOutput m (x_bits a) (r_bits a) (c1_bits a) (in_shares a) (acc3 a))
      input encBits := by
  let ePi := encPi (Index := Fin m) encBits
  have hot_c := comp' (fst ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hrest1 := comp' (snd ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hot_a := comp' (fst ePi (encPair ePi ePi)) hrest1
  have hrest2 := comp' (snd ePi (encPair ePi ePi)) hrest1
  have hout_m := comp' (fst ePi ePi) hrest2
  have hy_out := comp' (snd ePi ePi) hrest2
  have hviews := ofFn fun i =>
    computableTidilyInPolyTime_packPartyViewWord hx hr hc1 hot_c hin hot_a hout_m i
  have houts := ofFn fun i => comp' (pi_apply encBits i) hy_out
  simpa only [packRealOutput, List.ofFn_eq_map] using (hviews.prod houts).encoded

private theorem computableTidilyInPolyTime_packSimOutput {α : Type} {input : α ↪ List Bool}
    {m : ℕ} (I : Finset (Fin m))
    {x_bits r_bits c1_bits in_shares : α → Fin m → List Bool}
    {acc3 : α → Step3Acc m}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hacc3 : ComputableTidilyInPolyTime acc3 input (encStep3Acc m)) :
    ComputableTidilyInPolyTime
      (fun a => packSimOutput m I (x_bits a) (r_bits a) (c1_bits a) (in_shares a) (acc3 a))
      input encBits := by
  let ePi := encPi (Index := Fin m) encBits
  have hot_c := comp' (fst ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hrest1 := comp' (snd ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hot_a := comp' (fst ePi (encPair ePi ePi)) hrest1
  have hrest2 := comp' (snd ePi (encPair ePi ePi)) hrest1
  have hout_m := comp' (fst ePi ePi) hrest2
  have hviewsI : ComputableTidilyInPolyTime
      (fun a => List.ofFn fun i : Fin m =>
        if i ∈ I then
          packPartyViewWord (x_bits a) (r_bits a) (c1_bits a) (acc3 a).1
            (in_shares a) (acc3 a).2.1 (acc3 a).2.2.1 i
        else [])
      input (encList encBits) := by
    refine ofFn fun i => ?_
    by_cases hi : i ∈ I
    · simpa only [hi, ↓reduceIte] using
        computableTidilyInPolyTime_packPartyViewWord hx hr hc1 hot_c hin hot_a hout_m i
    · simpa only [hi, ↓reduceIte] using const (encIn := input) (encMid := encBits) ([] : List Bool)
  simpa only [packSimOutput, List.ofFn_eq_map] using hviewsI.encoded

private noncomputable def sampleTwoPiBits (m : ℕ) (w1 w2 : Fin m → ℕ) :
    ProbComp ((Fin m → List Bool) × (Fin m → List Bool)) := do
  let r ← OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (w1 i))
  (fun c => (r, c)) <$> OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (w2 i))

private theorem isPPTOn_sampleTwoPiBits {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {w1 w2 : α → Fin m → ℕ}
    (hw1 : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => w1 a i) input encUnary)
    (hw2 : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => w2 a i) input encUnary) :
    IsPPTOn input (encPair (encPi encBits) (encPi encBits))
      (fun a => sampleTwoPiBits m (w1 a) (w2 a)) := by
  let ePi := encPi (Index := Fin m) encBits
  have h1 := isPPTOn_pi_sampleList m hw1
  have h2 := isPPTOn_pi_sampleList (input := encPair input ePi) m
    (fun i => comp' (hw2 i) (fst input ePi))
  have h2_pair := h2.pair (snd input ePi)
  simpa only [sampleTwoPiBits, bind_map_left] using h1.keep_input.bind h2_pair

private theorem computableTidilyInPolyTime_familyRunInput_fst
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n : α → ℕ} :
    ComputableTidilyInPolyTime (fun inp : FamilyRunInput α m n => inp.1)
      (encFamilyRunInput encA m n) encA := by
  have hid : ComputableTidilyInPolyTime
      (fun inp : FamilyRunInput α m n =>
        (inp.1,
          List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n inp.1)).symm inp.2)))
      (encFamilyRunInput encA m n) (encPair encA encBits) :=
    of_eq fun _ => rfl
  have hres := comp' (fst encA encBits) hid
  exact hres

private theorem computableTidilyInPolyTime_familyRunInput_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilyRunInput α m n) (i : Fin m) => List.ofFn (inp.2 i))
      (encFamilyRunInput encA m n) (encPi encBits) := by
  have hid : ComputableTidilyInPolyTime
      (fun inp : FamilyRunInput α m n =>
        (inp.1,
          List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n inp.1)).symm inp.2)))
      (encFamilyRunInput encA m n) (encPair encA encBits) :=
    of_eq fun _ => rfl
  have ha := computableTidilyInPolyTime_familyRunInput_fst (encA := encA) (m := m) (n := n)
  have hword := comp' (snd encA encBits) hid
  refine pi fun i => ?_
  have hrow := bitsRowWithInput (comp' hn ha) (const i.val) hword
  convert hrow using 1
  funext inp
  rw [Cslib.BitString.listRow_eq_ofFn (n inp.1) i,
    Cslib.BitString.ofList_ofFn, Cslib.BitString.block_blocksEquiv_symm]

private theorem computableTidilyInPolyTime_familySimInput_fst
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k : α → ℕ} {I : Finset (Fin m)} :
    ComputableTidilyInPolyTime (fun inp : FamilySimInput α m n k I => inp.1)
      (encFamilySimInput encA m n k I) encA := by
  have hid : ComputableTidilyInPolyTime
      (fun inp : FamilySimInput α m n k I =>
        (inp.1, (extendCoalitionBits I inp.2.1, extendCoalitionBits I inp.2.2)))
      (encFamilySimInput encA m n k I) (encPair encA (encPair encBits encBits)) :=
    of_eq fun _ => rfl
  have hres := comp' (fst encA (encPair encBits encBits)) hid
  exact hres

private theorem listRow_extendCoalitionBits {m len : ℕ} (I : Finset (Fin m))
    (vI : (i : I) → BitString len) (i : Fin m) :
    Cslib.BitString.listRow len i.val (extendCoalitionBits I vI) =
      if hi : i ∈ I then List.ofFn (vI ⟨i, hi⟩) else List.replicate len false := by
  rw [extendCoalitionBits, Cslib.BitString.listRow_eq_ofFn len i,
    Cslib.BitString.ofList_ofFn, Cslib.BitString.block_blocksEquiv_symm]
  dsimp only [GMWCircuit.extendByZero]
  split_ifs with hi
  · rfl
  · exact List.ofFn_const len false

private theorem computableTidilyInPolyTime_familySimInput_x_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k : α → ℕ} {I : Finset (Fin m)}
    (hn : ComputableTidilyInPolyTime n encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilySimInput α m n k I) (i : Fin m) =>
        if hi : i ∈ I then List.ofFn (inp.2.1 ⟨i, hi⟩) else List.replicate (n inp.1) false)
      (encFamilySimInput encA m n k I) (encPi encBits) := by
  have hid : ComputableTidilyInPolyTime
      (fun inp : FamilySimInput α m n k I =>
        (inp.1, (extendCoalitionBits I inp.2.1, extendCoalitionBits I inp.2.2)))
      (encFamilySimInput encA m n k I) (encPair encA (encPair encBits encBits)) :=
    of_eq fun _ => rfl
  have ha := computableTidilyInPolyTime_familySimInput_fst
    (encA := encA) (m := m) (n := n) (k := k) (I := I)
  have hword := comp' (fst encBits encBits)
    (comp' (snd encA (encPair encBits encBits)) hid)
  refine pi fun i => ?_
  have hrow := bitsRowWithInput (comp' hn ha) (const i.val) hword
  convert hrow using 1
  funext inp
  exact (listRow_extendCoalitionBits I inp.2.1 i).symm

private theorem computableTidilyInPolyTime_familySimInput_y_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k : α → ℕ} {I : Finset (Fin m)}
    (hk : ComputableTidilyInPolyTime k encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilySimInput α m n k I) (i : Fin m) =>
        if hi : i ∈ I then List.ofFn (inp.2.2 ⟨i, hi⟩) else List.replicate (k inp.1) false)
      (encFamilySimInput encA m n k I) (encPi encBits) := by
  have hid : ComputableTidilyInPolyTime
      (fun inp : FamilySimInput α m n k I =>
        (inp.1, (extendCoalitionBits I inp.2.1, extendCoalitionBits I inp.2.2)))
      (encFamilySimInput encA m n k I) (encPair encA (encPair encBits encBits)) :=
    of_eq fun _ => rfl
  have ha := computableTidilyInPolyTime_familySimInput_fst
    (encA := encA) (m := m) (n := n) (k := k) (I := I)
  have hword := comp' (snd encBits encBits)
    (comp' (snd encA (encPair encBits encBits)) hid)
  refine pi fun i => ?_
  have hrow := bitsRowWithInput (comp' hk ha) (const i.val) hword
  convert hrow using 1
  funext inp
  exact (listRow_extendCoalitionBits I inp.2.2 i).symm

/-- Word-level runner for `Protocol.runEncoded` applied to `gmwOT14RandomizedProtocol` on a
polynomial-time circuit code family `D : α → List (Boolean.Op × List ℕ) × List ℕ`. -/
private noncomputable def realRunWord {α : Type} (m : ℕ) [NeZero m] (coins n k : α → ℕ)
    (D : α → List (Boolean.Op × List ℕ) × List ℕ)
    (inp : FamilyRunInput α m n) : WordOracleComp Unit (List Bool) := do
  let a := inp.1
  let x_bits : Fin m → List Bool := fun i => List.ofFn (inp.2 i)
  let rc ← ProbOracleComp.sample
    (sampleTwoPiBits m (fun _ => coins a) (fun _ => (n a + coins a) * (m - 1)))
  let in_shares := step1Wires m (n a + coins a) x_bits rc.1 rc.2
  let init2 : Step2Acc m := (in_shares, fun _ => [], fun _ => [])
  let acc2 ← foldlMList (realGateStep m) (D a).1 init2
  let outItems := buildOutItems m (k a) Finset.univ (D a).2 acc2.1 (fun _ => [])
  let init3 : Step3Acc m := (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
  let acc3 ← foldlMList (realOutStep m) outItems init3
  return packRealOutput m x_bits rc.1 rc.2 in_shares acc3

/-- Word-level simulator for `gmwOT14RandomizedSim` on a polynomial-time circuit code family
`D : α → List (Boolean.Op × List ℕ) × List ℕ`. -/
private noncomputable def simRunWord {α : Type} (m : ℕ) [NeZero m] (coins n k : α → ℕ)
    (D : α → List (Boolean.Op × List ℕ) × List ℕ)
    (I : Finset (Fin m)) (inp : FamilySimInput α m n k I) : ProbComp (List Bool) := do
  let a := inp.1
  let x_bits : Fin m → List Bool := fun i =>
    if hi : i ∈ I then List.ofFn (inp.2.1 ⟨i, hi⟩) else List.replicate (n a) false
  let y_bits : Fin m → List Bool := fun i =>
    if hi : i ∈ I then List.ofFn (inp.2.2 ⟨i, hi⟩) else List.replicate (k a) false
  let rc ← sampleTwoPiBits m (fun i => if i ∈ I then coins a else 0)
    (fun _ => (n a + coins a) * (m - 1))
  let in_shares := step1Wires m (n a + coins a) x_bits rc.1 rc.2
  let init2 : Step2Acc m := (in_shares, fun _ => [], fun _ => [])
  let acc2 ← foldlMList (simGateStep m I) (D a).1 init2
  let outItems := buildOutItems m (k a) I (D a).2 acc2.1 y_bits
  let init3 : Step3Acc m := (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
  let acc3 ← foldlMList (simOutStep m I) outItems init3
  return packSimOutput m I x_bits rc.1 rc.2 in_shares acc3

private theorem isOraclePPTOn_realRunWord {α : Type} {encA : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {D : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hcoins : ComputableTidilyInPolyTime coins encA encUnary)
    (hn : ComputableTidilyInPolyTime n encA encUnary)
    (hk : ComputableTidilyInPolyTime k encA encUnary)
    (hD : ComputableTidilyInPolyTime D encA Boolean.encCode) :
    IsOraclePPTOn (Operation := Unit) (encFamilyRunInput encA m n) encBits
      (realRunWord m coins n k D) := by
  let e0 := encFamilyRunInput encA m n
  let ePi := encPi (Index := Fin m) encBits
  let eRC := encPair ePi ePi
  let e1 := encPair e0 eRC
  let e2 := encPair e1 (encStep2Acc m)
  let e3 := encPair e2 (encStep3Acc m)
  have ha0 := computableTidilyInPolyTime_familyRunInput_fst (encA := encA) (m := m) (n := n)
  have hx0 := computableTidilyInPolyTime_familyRunInput_bits (encA := encA) (m := m) hn
  have hcoins0 := comp' hcoins ha0
  have hn0 := comp' hn ha0
  have hnc0 := comp' unary_add (hn0.prod hcoins0)
  have hw2_0 := comp' unary_mul (hnc0.prod (const (m - 1)))
  have hstage1 := ((isPPTOn_sampleTwoPiBits
    (fun _ : Fin m => hcoins0)
    (fun _ : Fin m => hw2_0)).isOraclePPTOn (Operation := Unit)).keep_input
  have hs1_inp := fst e0 eRC
  have hs1_rc := snd e0 eRC
  have ha1 := comp' ha0 hs1_inp
  have hx1 := comp' hx0 hs1_inp
  have hr1 := comp' (fst ePi ePi) hs1_rc
  have hc1 := comp' (snd ePi ePi) hs1_rc
  have hnc1 := comp' hnc0 hs1_inp
  have hin1 := computableTidilyInPolyTime_step1Wires m hnc1 hx1 hr1 hc1
  have hempty1 : ComputableTidilyInPolyTime
      (fun _ : FamilyRunInput α m n × ((Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun _ : Fin m => ([] : List Bool))) e1 ePi :=
    pi fun _ => const []
  have hinit2 := hin1.prod (hempty1.prod hempty1)
  have hD1_gates := comp' (fst (encList Boolean.encGate) (encList encNat)) (comp' hD ha1)
  have hstage2 := (isOraclePPTOn_foldlMList_of_bounded_growth (.const false, [])
    hD1_gates hinit2 (isOraclePPTOn_realGateStep m) (realGateStep_growth m)).keep_input
  have hs2_s1 := fst e1 (encStep2Acc m)
  have hs2_acc2 := snd e1 (encStep2Acc m)
  have ha2 := comp' ha1 hs2_s1
  have hk2 := comp' hk ha2
  have hD2_outs := comp' (snd (encList Boolean.encGate) (encList encNat)) (comp' hD ha2)
  have hwires2 := comp' (fst ePi (encPair ePi ePi)) hs2_acc2
  have hot_c2 := comp' (fst ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hot_a2 := comp' (snd ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hempty2 : ComputableTidilyInPolyTime
      (fun _ : (FamilyRunInput α m n × ((Fin m → List Bool) × (Fin m → List Bool))) × Step2Acc m =>
        (fun _ : Fin m => ([] : List Bool))) e2 ePi :=
    pi fun _ => const []
  have houtItems2 :=
    computableTidilyInPolyTime_buildOutItems m Finset.univ hk2 hD2_outs hwires2 hempty2
  have hinit3 := hot_c2.prod (hot_a2.prod (hempty2.prod hempty2))
  have hstage3 := (isOraclePPTOn_foldlMList_of_bounded_growth
    ((0, fun _ => false, false) : OutItem m)
    houtItems2 hinit3 (isOraclePPTOn_realOutStep m) (realOutStep_growth m)).keep_input
  have hs3_s1 := comp' hs2_s1 (fst e2 (encStep3Acc m))
  have hs3_acc3 := snd e2 (encStep3Acc m)
  have hx3 := comp' hx1 hs3_s1
  have hr3 := comp' hr1 hs3_s1
  have hc3 := comp' hc1 hs3_s1
  have hin3 := comp' hin1 hs3_s1
  have hpost := computableTidilyInPolyTime_packRealOutput hx3 hr3 hc3 hin3 hs3_acc3
  dsimp only [e0, ePi, eRC, e1, e2, e3] at hstage1 hstage2 hstage3 hpost
  have hres := ((hstage1.bind hstage2).bind hstage3).map hpost
  unfold realRunWord
  simpa only [bind_assoc, bind_map_left, map_bind, Functor.map_map, bind_pure_comp,
    Function.comp_def] using hres

private theorem isPPTOn_simRunWord {α : Type} {encA : α ↪ List Bool}
    (m : ℕ) [NeZero m] (I : Finset (Fin m)) {coins n k : α → ℕ}
    {D : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hcoins : ComputableTidilyInPolyTime coins encA encUnary)
    (hn : ComputableTidilyInPolyTime n encA encUnary)
    (hk : ComputableTidilyInPolyTime k encA encUnary)
    (hD : ComputableTidilyInPolyTime D encA Boolean.encCode) :
    IsPPTOn (encFamilySimInput encA m n k I) encBits
      (simRunWord m coins n k D I) := by
  let e0 := encFamilySimInput encA m n k I
  let ePi := encPi (Index := Fin m) encBits
  let eRC := encPair ePi ePi
  let e1 := encPair e0 eRC
  let e2 := encPair e1 (encStep2Acc m)
  let e3 := encPair e2 (encStep3Acc m)
  have ha0 := computableTidilyInPolyTime_familySimInput_fst
    (encA := encA) (m := m) (n := n) (k := k) (I := I)
  have hx0 := computableTidilyInPolyTime_familySimInput_x_bits
    (encA := encA) (m := m) (k := k) (I := I) hn
  have hy0 := computableTidilyInPolyTime_familySimInput_y_bits
    (encA := encA) (m := m) (n := n) (I := I) hk
  have hcoins0 := comp' hcoins ha0
  have hn0 := comp' hn ha0
  have hw1_0 : ∀ i : Fin m, ComputableTidilyInPolyTime
      (fun inp : FamilySimInput α m n k I => if i ∈ I then coins inp.1 else 0) e0 encUnary := by
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi, ↓reduceIte] using hcoins0
    · simpa only [hi, ↓reduceIte] using const (encIn := e0) (encMid := encUnary) 0
  have hnc0 := comp' unary_add (hn0.prod hcoins0)
  have hw2_0 := comp' unary_mul (hnc0.prod (const (m - 1)))
  have hstage1 := (isPPTOn_sampleTwoPiBits hw1_0 (fun _ : Fin m => hw2_0)).keep_input
  have hs1_inp := fst e0 eRC
  have hs1_rc := snd e0 eRC
  have ha1 := comp' ha0 hs1_inp
  have hx1 := comp' hx0 hs1_inp
  have hy1 := comp' hy0 hs1_inp
  have hr1 := comp' (fst ePi ePi) hs1_rc
  have hc1 := comp' (snd ePi ePi) hs1_rc
  have hnc1 := comp' hnc0 hs1_inp
  have hin1 := computableTidilyInPolyTime_step1Wires m hnc1 hx1 hr1 hc1
  have hempty1 : ComputableTidilyInPolyTime
      (fun _ : FamilySimInput α m n k I × ((Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun _ : Fin m => ([] : List Bool))) e1 ePi :=
    pi fun _ => const []
  have hinit2 := hin1.prod (hempty1.prod hempty1)
  have hD1_gates := comp' (fst (encList Boolean.encGate) (encList encNat)) (comp' hD ha1)
  have hstage2 := (isPPTOn_foldlMList_of_bounded_growth (.const false, [])
    hD1_gates hinit2 (isPPTOn_simGateStep m I) (simGateStep_growth m I)).keep_input
  have hs2_s1 := fst e1 (encStep2Acc m)
  have hs2_acc2 := snd e1 (encStep2Acc m)
  have ha2 := comp' ha1 hs2_s1
  have hk2 := comp' hk ha2
  have hy2 := comp' hy1 hs2_s1
  have hD2_outs := comp' (snd (encList Boolean.encGate) (encList encNat)) (comp' hD ha2)
  have hwires2 := comp' (fst ePi (encPair ePi ePi)) hs2_acc2
  have hot_c2 := comp' (fst ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hot_a2 := comp' (snd ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hempty2 : ComputableTidilyInPolyTime
      (fun _ :
        (FamilySimInput α m n k I × ((Fin m → List Bool) × (Fin m → List Bool))) × Step2Acc m =>
        (fun _ : Fin m => ([] : List Bool))) e2 ePi :=
    pi fun _ => const []
  have houtItems2 := computableTidilyInPolyTime_buildOutItems m I hk2 hD2_outs hwires2 hy2
  have hinit3 := hot_c2.prod (hot_a2.prod (hempty2.prod hempty2))
  have hstage3 := (isPPTOn_foldlMList_of_bounded_growth ((0, fun _ => false, false) : OutItem m)
    houtItems2 hinit3 (isPPTOn_simOutStep m I) (simOutStep_growth m I)).keep_input
  have hs3_s1 := comp' hs2_s1 (fst e2 (encStep3Acc m))
  have hs3_acc3 := snd e2 (encStep3Acc m)
  have hx3 := comp' hx1 hs3_s1
  have hr3 := comp' hr1 hs3_s1
  have hc3 := comp' hc1 hs3_s1
  have hin3 := comp' hin1 hs3_s1
  have hpost := computableTidilyInPolyTime_packSimOutput I hx3 hr3 hc3 hin3 hs3_acc3
  dsimp only [e0, ePi, eRC, e1, e2, e3] at hstage1 hstage2 hstage3 hpost
  have hres := ((hstage1.bind hstage2).bind hstage3).map (ComputableInPolyTime.of_tidy hpost)
  unfold simRunWord
  simpa only [bind_assoc, bind_map_left, map_bind, Functor.map_map, bind_pure_comp,
    Function.comp_def] using hres

/-! ### Section 4C: Equivalence of Word-Level Runners with `Protocol.runEncoded` and
`gmwOT14RandomizedSim` -/

/-- Concatenate `twoPartyMulProtocol` subcoin records along `sc₁ ++ sc₂`. -/
private def joinSubCoins2 {m : ℕ} :
    (sc₁ sc₂ : Schedule m (sharedMulSpec 2)) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₁ i →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₂ i →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) (sc₁ ++ sc₂) i
  | [], _, _, (), c₂ => c₂
  | .message _ _ _ :: sc₁, sc₂, i, c₁, c₂ => joinSubCoins2 sc₁ sc₂ i c₁ c₂
  | .oracle () _ :: sc₁, sc₂, i, (c_head, c_tail), c₂ =>
    (c_head, joinSubCoins2 sc₁ sc₂ i c_tail c₂)

/-- Concatenate received transcripts along
`Schedule.compose (fun _ => twoPartyMulSchedule) (sc₁ ++ sc₂)`. -/
private def joinReceived2 {m : ℕ} :
    (sc₁ sc₂ : Schedule m (sharedMulSpec 2)) → (i : Fin m) →
      (Schedule.compose (fun _ => twoPartyMulSchedule) sc₁).Received i →
      (Schedule.compose (fun _ => twoPartyMulSchedule) sc₂).Received i →
      (Schedule.compose (fun _ => twoPartyMulSchedule) (sc₁ ++ sc₂)).Received i
  | [], _, _, (), r₂ => r₂
  | .message _ _ _ :: sc₁, sc₂, i, (r_head, r_tail), r₂ =>
    (r_head, joinReceived2 sc₁ sc₂ i r_tail r₂)
  | .oracle () _ :: sc₁, sc₂, i, (r_head, r_tail), r₂ =>
    (r_head, joinReceived2 sc₁ sc₂ i r_tail r₂)

@[simp] private theorem encOTSubCoins_joinSubCoins2 {m : ℕ}
    (sc₁ sc₂ : Schedule m (sharedMulSpec 2)) (i : Fin m)
    (c₁ : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₁ i)
    (c₂ : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₂ i) :
    encOTSubCoins (sc₁ ++ sc₂) i (joinSubCoins2 sc₁ sc₂ i c₁ c₂) =
      encOTSubCoins sc₁ i c₁ ++ encOTSubCoins sc₂ i c₂ := by
  induction sc₁ with
  | nil =>
    cases c₁
    rfl
  | cons r sc₁ ih =>
    cases r with
    | message _ _ _ => exact ih c₁
    | oracle op parties =>
      cases op
      rcases c₁ with ⟨c_head, c_tail⟩
      simp [joinSubCoins2, encOTSubCoins, ih c_tail, List.append_assoc]

@[simp] private theorem encOTOracleAnswers_joinReceived2 {m : ℕ}
    (sc₁ sc₂ : Schedule m (sharedMulSpec 2)) (i : Fin m)
    (r₁ : (Schedule.compose (fun _ => twoPartyMulSchedule) sc₁).Received i)
    (r₂ : (Schedule.compose (fun _ => twoPartyMulSchedule) sc₂).Received i) :
    encOTOracleAnswers (sc₁ ++ sc₂) i (joinReceived2 sc₁ sc₂ i r₁ r₂) =
      encOTOracleAnswers sc₁ i r₁ ++ encOTOracleAnswers sc₂ i r₂ := by
  induction sc₁ with
  | nil =>
    cases r₁
    rfl
  | cons r sc₁ ih =>
    cases r with
    | message _ _ _ =>
      rcases r₁ with ⟨r_head, r_tail⟩
      exact ih r_tail
    | oracle op parties =>
      cases op
      rcases r₁ with ⟨r_head, r_tail⟩
      simp [joinReceived2, encOTOracleAnswers, ih r_tail, List.append_assoc]

/-- Join a received transcript along `((pairsSchedule L).map (Round.embed parties) ++ rest₁)`
with `b` into a transcript along `((pairsSchedule L).map (Round.embed parties) ++ rest₂)`. -/
private def joinPairsOTReceived {m : ℕ} {α : Type} (parties : Fin m ↪ Fin m) (i : Fin m) :
    (L : List (OrderedPair m)) → {rest₁ rest₂ : Schedule m (sharedMulSpec 2)} →
      ((Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → α →
        (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i) →
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        ((pairsSchedule L).map (Round.embed parties) ++ rest₁)).Received i →
      α →
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        ((pairsSchedule L).map (Round.embed parties) ++ rest₂)).Received i
  | [], _, _, k, r, b => k r b
  | _ :: L, _, _, k, (r_head, r_tail), b =>
    (r_head, joinPairsOTReceived parties i L k r_tail b)

/-- Join received transcripts along `otMulCompose a` and `otMulCompose b` into
`otMulCompose (a ++ b)`. -/
private def joinOTMulCompose {m : ℕ} :
    (a b : Schedule m (sharedMulSpec m)) → (i : Fin m) →
      (otMulCompose a).Received i → (otMulCompose b).Received i →
      (otMulCompose (a ++ b)).Received i
  | [], _, _, (), r_b => r_b
  | .message _ _ _ :: a, b, i, (r_head, r_tail), r_b =>
    (r_head, joinOTMulCompose a b i r_tail r_b)
  | .oracle () parties :: a, b, i, r_a, r_b =>
    joinPairsOTReceived parties i (orderedPairs m) (joinOTMulCompose a b i) r_a r_b

private theorem splitPairsOTReceived_joinPairsOTReceived {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_split : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i × α)
    (k_join : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (hk : ∀ r b, k_split (k_join r b) = (r, b))
    (r : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties) ++ rest₁)).Received i)
    (b : α) :
    splitPairsOTReceived parties i L k_split (joinPairsOTReceived parties i L k_join r b) =
      (r, b) := by
  induction L with
  | nil => exact hk r b
  | cons _ L ih =>
    rcases r with ⟨r_head, r_tail⟩
    simp [splitPairsOTReceived, joinPairsOTReceived, ih]

@[simp] private theorem splitOTMulCompose_joinOTMulCompose {m : ℕ}
    (a b : Schedule m (sharedMulSpec m)) (i : Fin m)
    (r_a : (otMulCompose a).Received i) (r_b : (otMulCompose b).Received i) :
    splitOTMulCompose a b i (joinOTMulCompose a b i r_a r_b) = (r_a, r_b) := by
  induction a generalizing r_b with
  | nil =>
    cases r_a
    rfl
  | cons r a ih =>
    cases r with
    | message _ _ _ =>
      rcases r_a with ⟨r_head, r_tail⟩
      simp [splitOTMulCompose, joinOTMulCompose, ih]
    | oracle op parties =>
      cases op
      exact splitPairsOTReceived_joinPairsOTReceived parties i (orderedPairs m)
        (splitOTMulCompose a b i) (joinOTMulCompose a b i) ih r_a r_b

private theorem joinPairsOTReceived_joinReceived2 {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_join : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (r₁ : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties))).Received i)
    (r_rest : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i)
    (b : α) :
    joinPairsOTReceived parties i L k_join
      (joinReceived2 ((pairsSchedule L).map (Round.embed parties)) rest₁ i r₁ r_rest) b =
    joinReceived2 ((pairsSchedule L).map (Round.embed parties)) rest₂ i r₁
      (k_join r_rest b) := by
  induction L with
  | nil =>
    cases r₁
    rfl
  | cons _ L ih =>
    rcases r₁ with ⟨r_head, r_tail⟩
    dsimp only [pairsSchedule, pairRound, List.map, List.append, Round.embed,
      joinPairsOTReceived, joinReceived2] at ih ⊢
    rw [ih r_tail]

private theorem encOTOracleAnswers_joinPairsOTReceived {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_join : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (f_b : α → List Bool)
    (hk : ∀ r b,
      encOTOracleAnswers rest₂ i (k_join r b) = encOTOracleAnswers rest₁ i r ++ f_b b)
    (r : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties) ++ rest₁)).Received i)
    (b : α) :
    encOTOracleAnswers ((pairsSchedule L).map (Round.embed parties) ++ rest₂) i
      (joinPairsOTReceived parties i L k_join r b) =
    encOTOracleAnswers ((pairsSchedule L).map (Round.embed parties) ++ rest₁) i r ++ f_b b := by
  induction L with
  | nil => exact hk r b
  | cons _ L ih =>
    rcases r with ⟨r_head, r_tail⟩
    dsimp only [pairsSchedule, pairRound, List.map, Round.embed,
      joinPairsOTReceived, encOTOracleAnswers] at ih ⊢
    simp [encOTOracleAnswers, ih r_tail, List.append_assoc]

@[simp] private theorem encOTOracleAnswers_joinOTMulCompose {m : ℕ}
    (a b : Schedule m (sharedMulSpec m)) (i : Fin m)
    (r_a : (otMulCompose a).Received i) (r_b : (otMulCompose b).Received i) :
    encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m) (a ++ b)) i
      (joinOTMulCompose a b i r_a r_b) =
    encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m) a) i r_a ++
      encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i r_b := by
  induction a generalizing r_b with
  | nil =>
    cases r_a
    rfl
  | cons r a ih =>
    cases r with
    | message _ _ _ =>
      rcases r_a with ⟨r_head, r_tail⟩
      exact ih r_tail r_b
    | oracle op parties =>
      cases op
      exact encOTOracleAnswers_joinPairsOTReceived parties i (orderedPairs m)
        (joinOTMulCompose a b i)
        (encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i)
        ih r_a r_b

/-- Join `twoPartyMulProtocol` subcoin records along
`((pairsSchedule L).map (Round.embed parties) ++ rest₁)`. -/
private def joinPairsOTSubCoins {m : ℕ} {α : Type} (parties : Fin m ↪ Fin m) (i : Fin m) :
    (L : List (OrderedPair m)) → {rest₁ rest₂ : Schedule m (sharedMulSpec 2)} →
      (Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₁ i → α →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₂ i) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        ((pairsSchedule L).map (Round.embed parties) ++ rest₁) i →
      α →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        ((pairsSchedule L).map (Round.embed parties) ++ rest₂) i
  | [], _, _, k, c, b => k c b
  | _ :: L, _, _, k, (c_head, c_tail), b =>
    (c_head, joinPairsOTSubCoins parties i L k c_tail b)

/-- Join `twoPartyMulProtocol` subcoin records along
`Schedule.compose (fun _ => multiPartyMulSchedule m) (a ++ b)`. -/
private def joinOTSubCoins {m : ℕ} :
    (a b : Schedule m (sharedMulSpec m)) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) a) i →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) (a ++ b)) i
  | [], _, _, (), c_b => c_b
  | .message _ _ _ :: a, b, i, c_a, c_b =>
    joinOTSubCoins a b i c_a c_b
  | .oracle () parties :: a, b, i, c_a, c_b =>
    joinPairsOTSubCoins parties i (orderedPairs m) (joinOTSubCoins a b i) c_a c_b

private theorem encOTSubCoins_joinPairsOTSubCoins {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_join : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₁ i → α →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₂ i)
    (f_b : α → List Bool)
    (hk : ∀ c b, encOTSubCoins rest₂ i (k_join c b) = encOTSubCoins rest₁ i c ++ f_b b)
    (c : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      ((pairsSchedule L).map (Round.embed parties) ++ rest₁) i)
    (b : α) :
    encOTSubCoins ((pairsSchedule L).map (Round.embed parties) ++ rest₂) i
      (joinPairsOTSubCoins parties i L k_join c b) =
    encOTSubCoins ((pairsSchedule L).map (Round.embed parties) ++ rest₁) i c ++ f_b b := by
  induction L with
  | nil => exact hk c b
  | cons _ L ih =>
    rcases c with ⟨c_head, c_tail⟩
    dsimp only [pairsSchedule, pairRound, List.map, Round.embed,
      joinPairsOTSubCoins, encOTSubCoins] at ih ⊢
    simp [encOTSubCoins, ih c_tail, List.append_assoc]

@[simp] private theorem encOTSubCoins_joinOTSubCoins {m : ℕ}
    (a b : Schedule m (sharedMulSpec m)) (i : Fin m)
    (c_a : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m) a) i)
    (c_b : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i) :
    encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m) (a ++ b)) i
      (joinOTSubCoins a b i c_a c_b) =
    encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m) a) i c_a ++
      encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i c_b := by
  induction a generalizing c_b with
  | nil =>
    cases c_a
    rfl
  | cons r a ih =>
    cases r with
    | message _ _ _ => exact ih c_a c_b
    | oracle op parties =>
      cases op
      exact encOTSubCoins_joinPairsOTSubCoins parties i (orderedPairs m)
        (joinOTSubCoins a b i)
        (encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m) b) i)
        ih c_a c_b

/-- Inline word-oracle execution of `Steps.compose (fun _ => twoPartyMulProtocol) steps₂`,
sampling each `twoPartyMulProtocol` sender coin `c₀ : Bool` on the fly at each `.oracle` round. -/
private noncomputable def runOTSteps {m : ℕ} {State Out : Fin m → Type}
    {sc₂ : Schedule m (sharedMulSpec 2)}
    (steps₂ : Steps State Out sc₂) (st : (i : Fin m) → State i) :
    WordOracleComp Unit
      (((i : Fin m) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₂ i) ×
       ((i : Fin m) → (Schedule.compose (fun _ => twoPartyMulSchedule) sc₂).Received i) ×
       ((i : Fin m) → Out i)) :=
  match steps₂ with
  | .done output =>
    pure (fun _ => (), fun _ => (), fun i => output i (st i))
  | .message (sender := s₀) (receiver := r₀) send next => do
    let r_head := Round.deliverMessage (spec := ot14Spec) (sender := s₀) (receiver := r₀)
      (send (st s₀))
    let cr_tail ← runOTSteps next (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
    return (cr_tail.1, fun i => (r_head i, cr_tail.2.1 i), cr_tail.2.2)
  | .oracle (op := ()) (parties := parties) query next => do
    let q : Fin 2 → Bool × Bool := fun s => query s (st (parties s))
    let c₀ ← ProbOracleComp.sample (ProbComp.uniform Bool)
    let rep ← List.take 1 <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), encodeOT14Query (fun s => twoPartyMulQuery s (q s, twoPartyMulCoins c₀ s)))
    let ans : Fin 2 → Bool := Fin.cases c₀ (fun _ => rep.headD false)
    let cr_tail ← runOTSteps next (fun i => (st i, Round.deliverOracle parties ans i))
    return (fun i => (Composition.pushTuple parties (twoPartyMulCoins c₀) i, cr_tail.1 i),
      fun i =>
        (Round.deliverOracle (spec := ot14Spec) (op := ())
          ((Function.Embedding.refl (Fin 2)).trans parties) (decodeOT14Reply rep) i,
         cr_tail.2.1 i),
      cr_tail.2.2)

@[simp] private theorem runOTSteps_mapState {m : ℕ} {State State' Out : Fin m → Type}
    {sc₂ : Schedule m (sharedMulSpec 2)}
    (f : (i : Fin m) → State i → State' i)
    (steps₂ : Steps State' Out sc₂) (st : (i : Fin m) → State i) :
    runOTSteps (steps₂.mapState f) st = runOTSteps steps₂ (fun i => f i (st i)) := by
  induction steps₂ generalizing State with
  | done output => rfl
  | message send next ih =>
    simp [Steps.mapState, runOTSteps, ih]
  | oracle query next ih =>
    simp [Steps.mapState, runOTSteps, ih]

private theorem runOTSteps_append {m : ℕ} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m (sharedMulSpec 2)}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (st : (i : Fin m) → State i) :
    runOTSteps (steps₁.append steps₂) st = (do
      let res₁ ← runOTSteps steps₁ st
      let res₂ ← runOTSteps steps₂ res₁.2.2
      return (fun i => joinSubCoins2 sc₁ sc₂ i (res₁.1 i) (res₂.1 i),
        fun i => joinReceived2 sc₁ sc₂ i (res₁.2.1 i) (res₂.2.1 i),
        res₂.2.2)) := by
  induction steps₁ with
  | done output =>
    simp [Steps.append, runOTSteps, runOTSteps_mapState, joinSubCoins2, joinReceived2]
  | message send next ih =>
    simp [Steps.append, runOTSteps, ih, joinSubCoins2, joinReceived2]
  | oracle query next ih =>
    simp [Steps.append, runOTSteps, ih, joinSubCoins2, joinReceived2]

private theorem eval_pi_single {m : ℕ} {β : Type} (i₀ : Fin m) (p : ProbComp β) :
    ProbComp.eval (OracleComp.pi fun i : Fin m =>
      if h : i₀ = i then
        (fun (c : β) (_ : i₀ = i) => c) <$> p
      else
        pure (fun h' : i₀ = i => (h h').elim)) =
      (ProbComp.eval p).map (fun (c : β) (i : Fin m) (_ : i₀ = i) => c) := by
  induction m with
  | zero => exact i₀.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j₀ => ?_) i₀
    · have h00 : (if h : (0 : Fin (m + 1)) = 0 then
          (fun (c : β) (_ : (0 : Fin (m + 1)) = 0) => c) <$> p
        else
          pure (fun h' : (0 : Fin (m + 1)) = 0 => (h h').elim)) =
          (fun (c : β) (_ : (0 : Fin (m + 1)) = 0) => c) <$> p := rfl
      have hrest : (fun i : Fin m =>
          if h : (0 : Fin (m + 1)) = i.succ then
            (fun (c : β) (_ : (0 : Fin (m + 1)) = i.succ) => c) <$> p
          else
            pure (fun h' : (0 : Fin (m + 1)) = i.succ => (h h').elim)) =
          fun i : Fin m =>
            pure (fun h' : (0 : Fin (m + 1)) = i.succ => (Fin.succ_ne_zero i h'.symm).elim) := by
        funext i
        have hne : ¬ ((0 : Fin (m + 1)) = i.succ) := fun h => Fin.succ_ne_zero i h.symm
        simp [hne]
      rw [OracleComp.pi_succ, h00, hrest]
      simp only [eval_pi_pure, ProbComp.eval_bind, ProbComp.eval_map, PMF.pure_map,
        PMF.bind_map, Function.comp_def]
      refine congrArg (PMF.map · (ProbComp.eval p)) (funext fun c => ?_)
      ext i h
      refine Fin.cases (fun _ => rfl) (fun j hj => (Fin.succ_ne_zero j hj.symm).elim) i h
    · have h0 : ¬ (j₀.succ = (0 : Fin (m + 1))) := Fin.succ_ne_zero j₀
      have h0_Br : (if h : j₀.succ = (0 : Fin (m + 1)) then
          (fun (c : β) (_ : j₀.succ = 0) => c) <$> p
        else
          pure (fun h' : j₀.succ = 0 => (h h').elim)) =
          pure (fun h' : j₀.succ = 0 => (h0 h').elim) := by
        simp [h0]
      have hrest : (fun i : Fin m =>
          if h : j₀.succ = i.succ then
            (fun (c : β) (_ : j₀.succ = i.succ) => c) <$> p
          else
            pure (fun h' : j₀.succ = i.succ => (h h').elim)) =
          fun i : Fin m =>
            (fun (f : (j₀ = i) → β) (h' : j₀.succ = i.succ) => f (Fin.succ_inj.1 h')) <$>
              (if h : j₀ = i then
                (fun (c : β) (_ : j₀ = i) => c) <$> p
              else
                pure (fun h' : j₀ = i => (h h').elim)) := by
        funext i
        by_cases h : j₀ = i
        · subst h
          simp [Functor.map_map]
        · have hs : ¬ (j₀.succ = i.succ) := fun hs => h (Fin.succ_inj.1 hs)
          simp [hs, h]
      rw [OracleComp.pi_succ, h0_Br, hrest]
      simp only [ProbComp.eval_pi_map, ih j₀,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.map_comp]
      refine congrArg (PMF.map · (ProbComp.eval p)) (funext fun c => ?_)
      ext i h
      refine Fin.cases (fun h0' => (h0 h0').elim) (fun _ _ => rfl) i h

private theorem eval_pi_sampleSlotCoins {k m : ℕ} (parties : Fin k ↪ Fin m)
    {Coins_k : Fin k → Type} (sample_k : (s : Fin k) → ProbComp (Coins_k s)) :
    ProbComp.eval (OracleComp.pi (Composition.sampleSlotCoins parties sample_k)) =
      (ProbComp.eval (OracleComp.pi sample_k)).map (Composition.pushTuple parties) := by
  unfold Composition.sampleSlotCoins
  rw [eval_pi_comm]
  have hpi := ProbComp.eval_pi_congr fun s : Fin k =>
    (eval_pi_single (parties s) (sample_k s)).trans (ProbComp.eval_map _ _).symm
  rw [hpi, ProbComp.eval_pi_map, PMF.map_comp]
  rfl

private theorem eval_pi_twoPartyMulSampleCoins :
    ProbComp.eval (OracleComp.pi twoPartyMulProtocol.sampleCoins) =
      ProbComp.eval (twoPartyMulCoins <$> ProbComp.uniform Bool) := by
  rw [ProbComp.eval_map, ProbComp.eval_uniform]
  ext r
  rw [ProbComp.eval_pi, PMF.pi_apply, Fin.prod_univ_two, PMF.map_apply]
  have hr : r = twoPartyMulCoins (r 0) := by
    ext i
    fin_cases i <;> rfl
  have h0 : ProbComp.eval (twoPartyMulProtocol.sampleCoins 0) (r 0) =
      PMF.uniformOfFintype Bool (r 0) :=
    congrFun (congrArg DFunLike.coe (ProbComp.eval_uniform (α := Bool))) (r 0)
  have h1 : ProbComp.eval (twoPartyMulProtocol.sampleCoins 1) (r 1) = 1 :=
    PMF.pure_apply_self ()
  rw [h0, h1, mul_one, tsum_bool]
  have hne : twoPartyMulCoins false ≠ twoPartyMulCoins true :=
    fun h => Bool.false_ne_true (congrFun h 0)
  cases hr0 : r 0
  · have heq : r = twoPartyMulCoins false := hr0 ▸ hr
    simp [heq, hne]
  · have heq : r = twoPartyMulCoins true := hr0 ▸ hr
    simp [heq, hne.symm]

private theorem runEncoded_twoPartyMulSteps (q : Fin 2 → Bool × Bool) (c₀ : Bool) :
    twoPartyMulProtocol.steps.runEncoded (fun s => (q s, twoPartyMulCoins c₀ s)) = (do
      let rep ← List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encodeOT14Query (fun s => twoPartyMulQuery s (q s, twoPartyMulCoins c₀ s)))
      return fun s =>
        (Round.deliverOracle (spec := ot14Spec) (op := ())
          (Function.Embedding.refl (Fin 2)) (decodeOT14Reply rep) s, ())) := by
  simp only [twoPartyMulProtocol, Steps.runEncoded, bind_pure_comp, map_pure]
  rfl

private theorem outputAt_twoPartyMulSteps (q : Fin 2 → Bool × Bool) (c₀ : Bool)
    (rep : List Bool) (s : Fin 2) :
    twoPartyMulProtocol.steps.outputAt s (q s, twoPartyMulCoins c₀ s)
      (Round.deliverOracle (spec := ot14Spec) (op := ())
        (Function.Embedding.refl (Fin 2)) (decodeOT14Reply rep) s, ()) =
    Fin.cases c₀ (fun _ => rep.headD false) s := by
  fin_cases s <;> rfl

private theorem outputAt_embed_twoPartyMul {m : ℕ} (parties : Fin 2 ↪ Fin m)
    (Outer : Fin m → Type) (i : Fin m) (out_i : Outer i)
    (q : Fin 2 → Bool × Bool) (c₀ : Bool) (rep : List Bool) :
    (Composition.Steps.embed parties Outer twoPartyMulProtocol.steps).outputAt i
      (out_i, fun (s : Fin 2) (_ : parties s = i) => (q s, twoPartyMulCoins c₀ s))
      (Composition.pushScheduleReceived parties twoPartyMulSchedule
        (fun s =>
          (Round.deliverOracle (spec := ot14Spec) (op := ())
            (Function.Embedding.refl (Fin 2)) (decodeOT14Reply rep) s, ())) i) =
      (out_i,
        Round.deliverOracle (spec := sharedMulSpec 2) (op := ()) parties
          (Fin.cases c₀ (fun _ => rep.headD false)) i) := by
  refine Prod.ext rfl (funext fun s => funext fun hs => ?_)
  subst hs
  exact outputAt_twoPartyMulSteps q c₀ rep s

private theorem runWith_sample_congr_eq {ι : Type} {spec : ι → Type} {α γ State : Type}
    (oracle : (i : ι) → StateT State PMF (spec i))
    (d₁ d₂ : ProbComp α) (heval : ProbComp.eval d₁ = ProbComp.eval d₂)
    (k : α → ProbOracleComp spec γ) (s : State) :
    ProbOracleComp.runWith oracle (ProbOracleComp.sample d₁ >>= k) s =
      ProbOracleComp.runWith oracle (ProbOracleComp.sample d₂ >>= k) s := by
  rw [runWith_sample_bind, runWith_sample_bind, heval]

private theorem runWith_sample_runEncoded_compose_twoPartyMul {m : ℕ} {OState : Type}
    {State Out : Fin m → Type} {sc₂ : Schedule m (sharedMulSpec 2)}
    (oracle : Unit × List Bool → StateT OState PMF (List Bool))
    (steps₂ : Steps State Out sc₂) (st : (i : Fin m) → State i) (s : OState) :
    ProbOracleComp.runWith oracle (do
      let c_ot ← ProbOracleComp.sample
        (OracleComp.pi (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol) sc₂))
      let recv ← (Composition.Steps.compose (fun _ => twoPartyMulProtocol) steps₂).runEncoded
        (fun i => (st i, c_ot i))
      return (c_ot, recv,
        fun i =>
          (Composition.Steps.compose (fun _ => twoPartyMulProtocol) steps₂).outputAt i
            (st i, c_ot i) (recv i))) s =
    ProbOracleComp.runWith oracle (runOTSteps steps₂ st) s := by
  induction steps₂ generalizing s with
  | done output =>
    have hpi :
        ProbComp.eval (OracleComp.pi
          (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
            ([] : Schedule m (sharedMulSpec 2)))) =
        ProbComp.eval (pure (fun _ : Fin m => ())) := by
      simp [Composition.sampleSubCoins, eval_pi_pure]
    rw [runWith_sample_congr_eq oracle _ _ hpi]
    simp [Composition.Steps.compose, Steps.runEncoded, Steps.outputAt, runOTSteps]
  | @message _ Out' s₀ r₀ Msg rest send next ih =>
    let f : ((i : Fin m) →
          Schedule.SubCoins (spec₁ := sharedMulSpec 2)
            (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest i) ×
        ((i : Fin m) → (Schedule.compose (fun _ => twoPartyMulSchedule) rest).Received i) ×
        ((i : Fin m) → Out' i) →
        ((i : Fin m) →
          Schedule.SubCoins (spec₁ := sharedMulSpec 2)
            (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
            (.message s₀ r₀ Msg :: rest) i) ×
        ((i : Fin m) →
          (Schedule.compose (fun _ => twoPartyMulSchedule)
            (.message s₀ r₀ Msg :: rest)).Received i) ×
        ((i : Fin m) → Out' i) :=
      fun res =>
        (res.1,
         fun i =>
           (Round.deliverMessage (spec := ot14Spec) (sender := s₀) (receiver := r₀)
              (send (st s₀)) i,
            res.2.1 i),
         res.2.2)
    have hlhs :
        (do
          let c_ot ← ProbOracleComp.sample
            (OracleComp.pi
              (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
                (.message s₀ r₀ Msg :: rest)))
          let recv ←
            (Composition.Steps.compose (fun _ => twoPartyMulProtocol)
              (Steps.message send next)).runEncoded (fun i => (st i, c_ot i))
          return (c_ot, recv,
            fun i =>
              (Composition.Steps.compose (fun _ => twoPartyMulProtocol)
                (Steps.message send next)).outputAt i (st i, c_ot i) (recv i))) =
        f <$> (do
          let c_ot ← ProbOracleComp.sample
            (OracleComp.pi (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol) rest))
          let recv ← (Composition.Steps.compose (fun _ => twoPartyMulProtocol) next).runEncoded
            (fun i => ((st i, Round.deliverMessage (send (st s₀)) i), c_ot i))
          return (c_ot, recv,
            fun i =>
              (Composition.Steps.compose (fun _ => twoPartyMulProtocol) next).outputAt i
                ((st i, Round.deliverMessage (send (st s₀)) i), c_ot i) (recv i))) := by
      simp only [f, Composition.Steps.compose, Composition.sampleSubCoins, Steps.runEncoded,
        Steps.runEncoded_mapState, Steps.outputAt, Steps.outputAt_mapState,
        map_bind, Functor.map_map, bind_pure_comp]
      rfl
    have hrhs :
        runOTSteps (Steps.message send next) st =
          f <$> runOTSteps next (fun i => (st i, Round.deliverMessage (send (st s₀)) i)) := by
      simp [f, runOTSteps]
    rw [hlhs, hrhs, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map]
    exact congrArg (Prod.map f id <$> ·)
      (ih (fun i => (st i, Round.deliverMessage (send (st s₀)) i)) s)
  | @oracle _ Out' op parties rest query next ih =>
    cases op
    let q : Fin 2 → Bool × Bool := fun t => query t (st (parties t))
    have hpi :
        ProbComp.eval (OracleComp.pi
          (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
            (.oracle () parties :: rest))) =
        ProbComp.eval (do
          let c₀ ← ProbComp.uniform Bool
          (fun c_tail i =>
            (Composition.pushTuple parties (twoPartyMulCoins c₀) i, c_tail i)) <$>
            OracleComp.pi
              (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol) rest)) := by
      simp only [Composition.sampleSubCoins, eval_pi_pair, eval_pi_sampleSlotCoins,
        eval_pi_twoPartyMulSampleCoins, ProbComp.eval_bind, ProbComp.eval_map,
        PMF.bind_map, PMF.map_comp, Function.comp_def]
    rw [runWith_sample_congr_eq oracle _ _ hpi, ProbOracleComp.sample_bind, bind_assoc]
    simp only [ProbOracleComp.sample_map, bind_map_left, runOTSteps]
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind]
    refine congrArg (Bind.bind (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) s)) (funext fun ⟨c₀, s₁⟩ => ?_)
    have hslot (i : Fin m) (t : Fin 2) (ht : parties t = i) :
        (query t (ht.symm ▸ st i), Composition.pushTuple parties (twoPartyMulCoins c₀) i t ht) =
          (q t, twoPartyMulCoins c₀ t) := by
      subst ht
      rfl
    have hst_k_i (c_tail : (i : Fin m) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest i) (i : Fin m) :
        ((st i, c_tail i),
          fun (t : Fin 2) (ht : parties t = i) =>
            (query t (ht.symm ▸ st i),
              Composition.pushTuple parties (twoPartyMulCoins c₀) i t ht)) =
        ((st i, c_tail i),
          fun (t : Fin 2) (_ : parties t = i) => (q t, twoPartyMulCoins c₀ t)) :=
      Prod.ext rfl (funext fun t => funext fun ht => hslot i t ht)
    simp only [Composition.Steps.compose, Steps.runEncoded_append, Steps.runEncoded_mapState,
      hst_k_i, Steps.runEncoded_embed, runEncoded_twoPartyMulSteps,
      Steps.outputAt_append, Steps.outputAt_mapState, outputAt_embed_twoPartyMul,
      bind_map_left, map_bind, bind_pure_comp, Functor.map_map]
    rw [runWith_sample_comm, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind]
    refine congrArg (PMF.bind _) (funext fun ⟨rep, s₂⟩ => ?_)
    let g : ((i : Fin m) →
          Schedule.SubCoins (spec₁ := sharedMulSpec 2)
            (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest i) ×
        ((i : Fin m) → (Schedule.compose (fun _ => twoPartyMulSchedule) rest).Received i) ×
        ((i : Fin m) → Out' i) →
        ((i : Fin m) →
          Schedule.SubCoins (spec₁ := sharedMulSpec 2)
            (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
            (.oracle () parties :: rest) i) ×
        ((i : Fin m) →
          (Schedule.compose (fun _ => twoPartyMulSchedule)
            (.oracle () parties :: rest)).Received i) ×
        ((i : Fin m) → Out' i) :=
      fun res =>
        (fun i => (Composition.pushTuple parties (twoPartyMulCoins c₀) i, res.1 i),
         fun i =>
           (Round.deliverOracle (spec := ot14Spec) (op := ())
              ((Function.Embedding.refl (Fin 2)).trans parties)
              (decodeOT14Reply (List.take 1 rep)) i,
            res.2.1 i),
         res.2.2)
    have hih := congrArg (PMF.map (Prod.map g id))
      (ih (fun i =>
        (st i,
          Round.deliverOracle (spec := sharedMulSpec 2) (op := ()) parties
            (Fin.cases c₀ (fun _ => (List.take 1 rep).headD false)) i)) s₂)
    rw [← ProbOracleComp.runWith_map, ← ProbOracleComp.runWith_map] at hih
    simp only [g, map_bind, bind_pure_comp, Functor.map_map] at hih
    exact hih

private theorem joinPairsOTSubCoins_joinSubCoins2 {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_join : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₁ i → α →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₂ i)
    (c₁ : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      ((pairsSchedule L).map (Round.embed parties)) i)
    (c_rest : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) rest₁ i)
    (b : α) :
    joinPairsOTSubCoins parties i L k_join
      (joinSubCoins2 ((pairsSchedule L).map (Round.embed parties)) rest₁ i c₁ c_rest) b =
    joinSubCoins2 ((pairsSchedule L).map (Round.embed parties)) rest₂ i c₁
      (k_join c_rest b) := by
  induction L with
  | nil =>
    cases c₁
    rfl
  | cons _ L ih =>
    rcases c₁ with ⟨c_head, c_tail⟩
    dsimp only [pairsSchedule, pairRound, List.map, List.append, Round.embed,
      joinPairsOTSubCoins, joinSubCoins2] at ih ⊢
    rw [ih c_tail]

/-- Canonical unit subcoin record for `multiPartyMulProtocol m` (whose `Coins` type is `Unit`). -/
private def unitSubCoins {m : ℕ} :
    (sc : Schedule m (sharedMulSpec m)) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec m) (fun _ _ => Unit) sc i
  | [], _ => ()
  | .message _ _ _ :: sc, i => unitSubCoins sc i
  | .oracle () _ :: sc, i => (fun _ _ => (), unitSubCoins sc i)

private theorem eval_sampleSubCoins_multiPartyMul {m : ℕ}
    (sc : Schedule m (sharedMulSpec m)) (i : Fin m) :
    ProbComp.eval
      (Composition.sampleSubCoins (fun _ : Unit => multiPartyMulProtocol m) sc i) =
    ProbComp.eval (pure (unitSubCoins sc i)) := by
  induction sc with
  | nil => rfl
  | cons r sc ih =>
    cases r with
    | message _ _ _ => exact ih
    | oracle op parties =>
      cases op
      have hslot :
          ProbComp.eval
            (Composition.sampleSlotCoins parties (multiPartyMulProtocol m).sampleCoins i) =
          ProbComp.eval (pure (fun _ _ => ())) := by
        unfold Composition.sampleSlotCoins
        have hcongr :
            ∀ s : Fin m,
              ProbComp.eval
                (if h : parties s = i then
                  (fun (c : Unit) (_ : parties s = i) => c) <$>
                    (multiPartyMulProtocol m).sampleCoins s
                else
                  pure (fun h' : parties s = i => (h h').elim)) =
              ProbComp.eval (pure (fun _ : parties s = i => ())) := by
          intro s
          by_cases h : parties s = i <;> simp [h, multiPartyMulProtocol]
        rw [ProbComp.eval_pi_congr hcongr, eval_pi_pure, ProbComp.eval_pure]
      simp [Composition.sampleSubCoins, hslot, ih, unitSubCoins]

private theorem eval_pi_sampleSubCoins_multiPartyMul {m : ℕ}
    (sc : Schedule m (sharedMulSpec m)) :
    ProbComp.eval
      (OracleComp.pi
        (Composition.sampleSubCoins (fun _ : Unit => multiPartyMulProtocol m) sc)) =
    ProbComp.eval (pure (unitSubCoins sc)) := by
  rw [ProbComp.eval_pi_congr (eval_sampleSubCoins_multiPartyMul sc),
    eval_pi_pure, ProbComp.eval_pure]

/-- Inline word-oracle execution of `steps : Steps State Out sc` composed with
`multiPartyMulProtocol m` and `twoPartyMulProtocol`. -/
private noncomputable def runSharedMulSteps {m : ℕ} {State Out : Fin m → Type}
    {sc : Schedule m (sharedMulSpec m)}
    (steps : Steps State Out sc) (st : (i : Fin m) → State i) :
    WordOracleComp Unit
      (((i : Fin m) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m) sc) i) ×
       ((i : Fin m) → (otMulCompose sc).Received i) ×
       ((i : Fin m) → Out i)) :=
  runOTSteps
    (Composition.Steps.compose (fun _ => multiPartyMulProtocol m) steps)
    (fun i => (st i, unitSubCoins sc i))

private theorem runOTSteps_embed {k m : ℕ} (parties : Fin k ↪ Fin m)
    (Outer : Fin m → Type) {State_k Out_k : Fin k → Type}
    {sc_k : Schedule k (sharedMulSpec 2)}
    (sub_steps : Steps State_k Out_k sc_k)
    (out_i : (i : Fin m) → Outer i)
    (st_k : (i : Fin m) → (s : Fin k) → (parties s = i) → State_k s) :
    runOTSteps (Composition.Steps.embed parties Outer sub_steps)
      (fun i => (out_i i, st_k i)) =
    (fun res =>
      (res.1, res.2.1, fun i => (out_i i, (res.2.2 i).2))) <$>
      runOTSteps (Composition.Steps.embed parties (fun _ => Unit) sub_steps)
        (fun i => ((), st_k i)) := by
  induction sub_steps with
  | done output =>
    simp [Composition.Steps.embed, runOTSteps]
  | message send next ih =>
    simp [Composition.Steps.embed, runOTSteps, ih]
  | oracle query next ih =>
    rcases ‹(sharedMulSpec 2).Op› with ⟨⟩
    simp [Composition.Steps.embed, runOTSteps, ih]

@[simp] private theorem runSharedMulSteps_mapState {m : ℕ}
    {State State' Out : Fin m → Type} {sc : Schedule m (sharedMulSpec m)}
    (f : (i : Fin m) → State i → State' i)
    (steps : Steps State' Out sc) (st : (i : Fin m) → State i) :
    runSharedMulSteps (steps.mapState f) st =
      runSharedMulSteps steps (fun i => f i (st i)) := by
  induction steps generalizing State with
  | done output => rfl
  | message send next ih =>
    have hih := ih (fun i (p : State i × _) => (f i p.1, p.2))
      (fun i => (st i, Round.deliverMessage (send (f _ (st _))) i))
    simp only [runSharedMulSteps, Steps.mapState, Composition.Steps.compose,
      unitSubCoins, runOTSteps, runOTSteps_mapState] at hih ⊢
    exact congrArg (Bind.bind · _) hih
  | @oracle _ _ op parties rest query next ih =>
    cases op
    have hst :
        (fun i : Fin m =>
          ((), fun (s : Fin m) (hs : parties s = i) =>
            (query s (f (parties s) (hs.symm ▸ st i)), ()))) =
        fun i : Fin m =>
          ((), fun (s : Fin m) (hs : parties s = i) =>
            (query s (hs.symm ▸ f i (st i)), ())) := by
      funext i
      refine Prod.ext rfl (funext fun s => funext fun hs => ?_)
      subst hs
      rfl
    simp only [runSharedMulSteps, Steps.mapState, Composition.Steps.compose,
      unitSubCoins, runOTSteps_append, runOTSteps_mapState]
    conv_lhs => arg 1; rw [runOTSteps_embed]
    conv_rhs => arg 1; rw [runOTSteps_embed]
    simp only [hst, bind_map_left]
    refine congrArg (Bind.bind _) (funext fun res₁ => ?_)
    have hih := ih (fun i (p : State i × _) => (f i p.1, p.2))
      (fun i => (st i, (res₁.2.2 i).2))
    simp only [runSharedMulSteps] at hih
    exact congrArg (Bind.bind · _) hih

private theorem runSharedMulSteps_append {m : ℕ} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m (sharedMulSpec m)}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (st : (i : Fin m) → State i) :
    runSharedMulSteps (steps₁.append steps₂) st = (do
      let res₁ ← runSharedMulSteps steps₁ st
      let res₂ ← runSharedMulSteps steps₂ res₁.2.2
      return (fun i => joinOTSubCoins sc₁ sc₂ i (res₁.1 i) (res₂.1 i),
        fun i => joinOTMulCompose sc₁ sc₂ i (res₁.2.1 i) (res₂.2.1 i),
        res₂.2.2)) := by
  induction steps₁ with
  | done output =>
    rw [Steps.append, runSharedMulSteps_mapState]
    simp [runSharedMulSteps, Composition.Steps.compose, unitSubCoins, runOTSteps,
      joinOTSubCoins, joinOTMulCompose]
  | message send next ih =>
    simp only [Steps.append, List.append_eq, List.cons_append, runSharedMulSteps,
      Composition.Steps.compose, unitSubCoins, runOTSteps, runOTSteps_mapState,
      joinOTSubCoins, joinOTMulCompose, bind_assoc, pure_bind] at ih ⊢
    rw [ih]
    simp
  | @oracle _ _ op parties rest query next ih =>
    cases op
    simp only [Steps.append, List.append_eq, List.cons_append, runSharedMulSteps,
      Composition.Steps.compose, unitSubCoins, runOTSteps_append, runOTSteps_mapState,
      bind_assoc] at ih ⊢
    conv_lhs => arg 1; rw [runOTSteps_embed]
    conv_rhs => arg 1; rw [runOTSteps_embed]
    simp only [bind_map_left]
    refine congrArg (Bind.bind _) (funext fun res_embed => ?_)
    have hih := ih steps₂ (fun i => (st i, (res_embed.2.2 i).2))
    rw [hih]
    simp only [bind_assoc, pure_bind, joinOTSubCoins, joinOTMulCompose,
      joinPairsOTSubCoins_joinSubCoins2, joinPairsOTReceived_joinReceived2]
    rfl

/-- Deterministic coalition simulator expansion along `sc₂ : Schedule m (sharedMulSpec 2)`
for `twoPartyMulSim`. -/
private def detExpandOTSim {m : ℕ} (I : Finset (Fin m)) :
    (sc₂ : Schedule m (sharedMulSpec 2)) →
      ((i : I) → sc₂.Received i.1) →
      (i : I) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc₂ i.1 ×
        (Schedule.compose (fun _ => twoPartyMulSchedule) sc₂).Received i.1
  | [], _ => fun _ => ((), ())
  | .message _ _ _ :: sc₂, recvI =>
    let rest := detExpandOTSim I sc₂ (fun i => (recvI i).2)
    fun i => ((rest i).1, ((recvI i).1, (rest i).2))
  | .oracle () parties :: sc₂, recvI =>
    let J := Composition.subCoalition parties I
    let aJ : (s : J) → Bool :=
      fun s => (recvI ⟨parties s.1, Composition.mem_subCoalition.1 s.2⟩).1 s.1 rfl
    let rest := detExpandOTSim I sc₂ (fun i => (recvI i).2)
    fun i =>
      ((Composition.pushTupleRestrict parties I
          (fun s => twoPartyMulCoins (aJ s) s.1) i,
        (rest i).1),
       (Composition.pushRoundReceivedRestrict parties I
          (.oracle (spec := ot14Spec) () (Function.Embedding.refl (Fin 2)))
          (fun s => twoPartyMulReceived s.1 (aJ s)) i,
        (rest i).2))

private theorem expandSimSteps_twoPartyMulSim {m : ℕ} {State Out : Fin m → Type}
    {sc₂ : Schedule m (sharedMulSpec 2)} (I : Finset (Fin m))
    (steps₂ : Steps State Out sc₂) (stI : (i : I) → State i.1)
    (recvI : (i : I) → sc₂.Received i.1) :
    Composition.expandSimSteps (fun _ => twoPartyMulSim) I steps₂ stI recvI =
      pure (detExpandOTSim I sc₂ recvI) := by
  induction steps₂ with
  | done _ => rfl
  | message _ next ih =>
    simp [Composition.expandSimSteps, ih, detExpandOTSim]
  | oracle query next ih =>
    rcases ‹(sharedMulSpec 2).Op› with ⟨⟩
    simp [Composition.expandSimSteps, twoPartyMulSim, twoPartyMulViewOfInOut,
      ih, detExpandOTSim, Composition.pushScheduleReceivedRestrict, Schedule.Received.append]

private theorem detExpandOTSim_append {m : ℕ} (I : Finset (Fin m))
    (sc₁ sc₂ : Schedule m (sharedMulSpec 2))
    (r₁ : (i : I) → sc₁.Received i.1) (r₂ : (i : I) → sc₂.Received i.1) (i : I) :
    detExpandOTSim I (sc₁ ++ sc₂) (fun j => Schedule.Received.append (r₁ j) (r₂ j)) i =
      (joinSubCoins2 sc₁ sc₂ i.1 (detExpandOTSim I sc₁ r₁ i).1 (detExpandOTSim I sc₂ r₂ i).1,
       joinReceived2 sc₁ sc₂ i.1 (detExpandOTSim I sc₁ r₁ i).2 (detExpandOTSim I sc₂ r₂ i).2) := by
  induction sc₁ with
  | nil =>
    have hr : (fun j : I => Schedule.Received.append (r₁ j) (r₂ j)) = r₂ := by
      funext j
      cases r₁ j
      rfl
    rw [hr]
    rfl
  | cons r sc₁ ih =>
    have hih := ih (fun j => (r₁ j).2)
    cases r with
    | message _ _ _ =>
      simp [detExpandOTSim, Schedule.Received.append, joinSubCoins2, joinReceived2, hih]
    | oracle op parties =>
      cases op
      simp [detExpandOTSim, Schedule.Received.append, joinSubCoins2, joinReceived2, hih]

/-- Simulated subcoins and `ot14Spec` received transcripts along `steps : Steps State Out sc`
for coalition `I`. -/
private noncomputable def simSharedMulSteps {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    {sc : Schedule m (sharedMulSpec m)} (I : Finset (Fin m))
    (steps : Steps State Out sc)
    (stI : (i : I) → State i.1) (recvI : (i : I) → sc.Received i.1) :
    ProbComp ((i : I) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) sc) i.1 ×
      (otMulCompose sc).Received i.1) :=
  (fun sub =>
    detExpandOTSim I (Schedule.compose (fun _ => multiPartyMulSchedule m) sc)
      (fun i => (sub i).2)) <$>
    Composition.expandSimSteps (fun _ => multiPartyMulSim m) I steps stI recvI

private theorem expandSimSteps_mapState {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {State State' Out : Fin m → Type} {sc : Schedule m spec₁}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (f : (i : Fin m) → State i → State' i)
    (steps : Steps State' Out sc)
    (stI : (i : I) → State i.1) (recvI : (i : I) → sc.Received i.1) :
    Composition.expandSimSteps S₂ I (steps.mapState f) stI recvI =
      Composition.expandSimSteps S₂ I steps (fun i => f i.1 (stI i)) recvI := by
  induction steps generalizing State with
  | done _ => rfl
  | message _ next ih =>
    simp [Steps.mapState, Composition.expandSimSteps,
      ih (fun i (p : State i × _) => (f i p.1, p.2))]
  | oracle _ next ih =>
    simp [Steps.mapState, Composition.expandSimSteps,
      ih (fun i (p : State i × _) => (f i p.1, p.2))]

@[simp] private theorem simSharedMulSteps_mapState {m : ℕ} [NeZero m]
    {State State' Out : Fin m → Type} {sc : Schedule m (sharedMulSpec m)}
    (I : Finset (Fin m)) (f : (i : Fin m) → State i → State' i)
    (steps : Steps State' Out sc)
    (stI : (i : I) → State i.1) (recvI : (i : I) → sc.Received i.1) :
    simSharedMulSteps I (steps.mapState f) stI recvI =
      simSharedMulSteps I steps (fun i => f i.1 (stI i)) recvI := by
  simp [simSharedMulSteps, expandSimSteps_mapState]

@[simp] private theorem simSharedMulSteps_done {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    (I : Finset (Fin m)) (output : (i : Fin m) → State i → Out i)
    (stI : (i : I) → State i.1)
    (recvI : (i : I) → Schedule.Received ([] : Schedule m (sharedMulSpec m)) i.1) :
    simSharedMulSteps I (.done output) stI recvI = pure (fun _ => ((), ())) := by
  simp [simSharedMulSteps, Composition.expandSimSteps, detExpandOTSim]

private theorem simSharedMulSteps_message {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    {s₀ r₀ : Fin m} {Msg : Type} {rest : Schedule m (sharedMulSpec m)}
    (I : Finset (Fin m)) (send : State s₀ → Msg)
    (next : Steps (fun i => State i × (Round.message s₀ r₀ Msg).Received i) Out rest)
    (stI : (i : I) → State i.1)
    (recvI : (i : I) → Schedule.Received (Round.message s₀ r₀ Msg :: rest) i.1) :
    simSharedMulSteps I (.message send next) stI recvI =
      (fun res (i : I) => ((res i).1, ((recvI i).1, (res i).2))) <$>
        simSharedMulSteps I next (fun i => (stI i, (recvI i).1)) (fun i => (recvI i).2) := by
  simp [simSharedMulSteps, Composition.expandSimSteps, detExpandOTSim, Functor.map_map]

private theorem simSharedMulSteps_oracle {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    {parties : Fin m ↪ Fin m} {rest : Schedule m (sharedMulSpec m)}
    (I : Finset (Fin m))
    (query : (s : Fin m) → State (parties s) → Bool × Bool)
    (next : Steps
      (fun i => State i × (Round.oracle (spec := sharedMulSpec m) () parties).Received i)
      Out rest)
    (stI : (i : I) → State i.1)
    (recvI : (i : I) →
      Schedule.Received (Round.oracle (spec := sharedMulSpec m) () parties :: rest) i.1) :
    simSharedMulSteps I (.oracle (op := ()) query next) stI recvI = (do
      let J := Composition.subCoalition parties I
      let qJ : (s : J) → Bool × Bool :=
        fun s => query s.1 (stI ⟨parties s.1, Composition.mem_subCoalition.1 s.2⟩)
      let aJ : (s : J) → Bool :=
        fun s => (recvI ⟨parties s.1, Composition.mem_subCoalition.1 s.2⟩).1 s.1 rfl
      let v_sub ← multiPartyMulSim m J qJ aJ
      let ot_head := detExpandOTSim I ((multiPartyMulSchedule m).map (Round.embed parties))
        (Composition.pushScheduleReceivedRestrict parties I (multiPartyMulSchedule m)
          (fun s => (v_sub s).received))
      let res_tail ← simSharedMulSteps I next (fun i => (stI i, (recvI i).1)) (fun i => (recvI i).2)
      return fun i =>
        (joinSubCoins2 ((multiPartyMulSchedule m).map (Round.embed parties))
          (Schedule.compose (fun _ => multiPartyMulSchedule m) rest) i.1
          (ot_head i).1 (res_tail i).1,
         joinReceived2 ((multiPartyMulSchedule m).map (Round.embed parties))
          (Schedule.compose (fun _ => multiPartyMulSchedule m) rest) i.1
          (ot_head i).2 (res_tail i).2)) := by
  simp only [simSharedMulSteps, Composition.expandSimSteps, Schedule.compose,
    map_bind, Functor.map_map, bind_pure_comp]
  refine congrArg (Bind.bind _) (funext fun v_sub => ?_)
  refine congrArg (· <$> _) (funext fun sub => funext fun i => ?_)
  exact detExpandOTSim_append I ((multiPartyMulSchedule m).map (Round.embed parties))
    (Schedule.compose (fun _ => multiPartyMulSchedule m) rest) _ (fun j => (sub j).2) i

private theorem simSharedMulSteps_append {m : ℕ} [NeZero m] {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m (sharedMulSpec m)} (I : Finset (Fin m))
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (stI : (i : I) → State i.1)
    (r₁ : (i : I) → sc₁.Received i.1) (r₂ : (i : I) → sc₂.Received i.1) :
    simSharedMulSteps I (steps₁.append steps₂) stI
      (fun i => Schedule.Received.append (r₁ i) (r₂ i)) = (do
      let res₁ ← simSharedMulSteps I steps₁ stI r₁
      let res₂ ← simSharedMulSteps I steps₂ (fun i => steps₁.outputAt i.1 (stI i) (r₁ i)) r₂
      return fun i =>
        (joinOTSubCoins sc₁ sc₂ i.1 (res₁ i).1 (res₂ i).1,
         joinOTMulCompose sc₁ sc₂ i.1 (res₁ i).2 (res₂ i).2)) := by
  induction steps₁ with
  | done output =>
    have hr : (fun i : I => Schedule.Received.append (r₁ i) (r₂ i)) = r₂ := by
      funext i
      cases r₁ i
      rfl
    rw [Steps.append, hr, simSharedMulSteps_mapState, simSharedMulSteps_done]
    simp [Steps.outputAt, joinOTSubCoins, joinOTMulCompose]
  | message send next ih =>
    simp only [Steps.append, List.append_eq, List.cons_append, Schedule.Received.append,
      simSharedMulSteps_message, ih, Steps.outputAt,
      map_bind, bind_map_left, Functor.map_map, bind_pure_comp,
      joinOTSubCoins, joinOTMulCompose]
  | @oracle _ _ op parties rest query next ih =>
    cases op
    simp only [Steps.append, List.append_eq, List.cons_append, Schedule.Received.append,
      simSharedMulSteps_oracle, ih, Steps.outputAt,
      bind_assoc, map_bind, bind_map_left, Functor.map_map, bind_pure_comp,
      joinOTSubCoins, joinOTMulCompose,
      joinPairsOTSubCoins_joinSubCoins2, joinPairsOTReceived_joinReceived2]

private theorem dropPairsOTReceived_joinPairsOTReceived {m : ℕ} {α : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k_join : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (r : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties) ++ rest₁)).Received i)
    (b : α) :
    dropPairsOTReceived parties i L (joinPairsOTReceived parties i L k_join r b) =
      k_join (dropPairsOTReceived parties i L r) b := by
  induction L with
  | nil => rfl
  | cons _ L ih =>
    rcases r with ⟨r_head, r_tail⟩
    dsimp only [pairsSchedule, pairRound, List.map, List.append, Round.embed,
      dropPairsOTReceived, joinPairsOTReceived] at ih ⊢
    exact ih r_tail

private theorem encOutCoordsMsgReceived_joinOTMulCompose {m k : ℕ} (i : Fin m)
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k))
    (r_ot : (otMulCompose [.oracle () (Function.Embedding.refl (Fin m))]).Received i)
    (r_gather : (otMulCompose (GMWCircuit.gatherSchedule m coord.1 (List.finRange m))).Received i)
    (r_L : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) :
    encOutCoordsMsgReceived i (coord :: L)
      (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L) i
        (joinOTMulCompose [.oracle () (Function.Embedding.refl (Fin m))]
          (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i r_ot r_gather)
        r_L) =
      encGatherOTReceived coord.1 i (List.finRange m) r_gather ++
        encOutCoordsMsgReceived i L r_L := by
  simp [encOutCoordsMsgReceived, joinOTMulCompose, dropPairsOTReceived_joinPairsOTReceived]

/-! ### Sub-part 4C.2: One `sharedMulSpec m` Round & Step 1 Input Sharing -/

private theorem runOTSteps_embed_mapState {k m : ℕ}
    (parties : Fin k ↪ Fin m) (Outer : Fin m → Type)
    {State_k State_k' Out_k : Fin k → Type} {sc_k : Schedule k (sharedMulSpec 2)}
    (g : (s : Fin k) → State_k' s → State_k s)
    (steps : Steps State_k Out_k sc_k)
    (st : (i : Fin m) → Outer i × ((s : Fin k) → (parties s = i) → State_k' s)) :
    runOTSteps (Composition.Steps.embed parties Outer (steps.mapState g)) st =
      runOTSteps (Composition.Steps.embed parties Outer steps)
        (fun i => ((st i).1, fun s hs => g s ((st i).2 s hs))) := by
  induction steps generalizing State_k' with
  | done output => rfl
  | message send next ih =>
    simp [Steps.mapState, Composition.Steps.embed, runOTSteps,
      ih (fun s (p : State_k' s × _) => (g s p.1, p.2))]
  | oracle query next ih =>
    rcases ‹(sharedMulSpec 2).Op› with ⟨⟩
    simp [Steps.mapState, Composition.Steps.embed, runOTSteps,
      ih (fun s (p : State_k' s × _) => (g s p.1, p.2))]

@[simp] private theorem encOTSubCoins_nil {m : ℕ} (i : Fin m) :
    encOTSubCoins ([] : Schedule m (sharedMulSpec 2)) i () = [] := rfl

@[simp] private theorem encOTOracleAnswers_nil {m : ℕ} (i : Fin m) :
    encOTOracleAnswers ([] : Schedule m (sharedMulSpec 2)) i () = [] := rfl

private theorem extractPairShare_pullRoundReceived_deliverOracle {m : ℕ}
    (p : OrderedPair m) (c₀ ans_v : Bool) (s i : Fin m)
    (hs : (Function.Embedding.refl (Fin m)) s = i) :
    extractPairShare p s
      (Composition.pullRoundReceived (Function.Embedding.refl (Fin m)) (pairRound p) hs
        (Round.deliverOracle (spec := sharedMulSpec 2) (op := ())
          ((pairEmbedding p).trans (Function.Embedding.refl (Fin m)))
          (Fin.cases c₀ (fun _ => ans_v)) i)) =
      if p.1.1 = s then c₀ else if p.1.2 = s then ans_v else 0 := by
  change s = i at hs
  subst hs
  dsimp [extractPairShare, Composition.pullRoundReceived, Round.deliverOracle]
  split_ifs <;> rfl

private theorem runOTSteps_embed_pairsSteps {m : ℕ}
    (x : Fin m → Bool × Bool) {L : List (OrderedPair m)} (hL : L.Nodup)
    (acc : Fin m → Bool) :
    ((fun res =>
      (fun i => (res.2.2 i).2 i rfl,
       fun i =>
        encOTSubCoins
          ((pairsSchedule L).map (Round.embed (Function.Embedding.refl (Fin m))))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          ((pairsSchedule L).map (Round.embed (Function.Embedding.refl (Fin m))))
          i (res.2.1 i))) <$>
      runOTSteps
        (Composition.Steps.embed (Function.Embedding.refl (Fin m)) (fun _ => Unit) (pairsSteps L))
        (fun i =>
          ((), fun (s : Fin m) (_ : (Function.Embedding.refl (Fin m)) s = i) => (x s, acc s)))) =
    (fun tr =>
      (fun i =>
        acc i +
          (L.map fun p =>
            if p.1.1 = i then (tr p).1 else if p.1.2 = i then (tr p).2 else 0).sum,
       fun i => (L.map fun p => if p.1.1 = i then [(tr p).1] else []).flatten,
       fun i => (L.map fun p => if p.1.2 = i then [(tr p).2] else []).flatten)) <$>
      realPairsCalls m x L := by
  induction L generalizing acc with
  | nil =>
    simp only [pairsSchedule, pairsSteps, Composition.Steps.embed, runOTSteps, realPairsCalls,
      List.map_nil, List.sum_nil, add_zero, List.flatten_nil, map_pure]
    rfl
  | cons p L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hp, hL⟩ := hL
    let acc' (c₀ ans_v : Bool) (s : Fin m) : Bool :=
      acc s + (if p.1.1 = s then c₀ else if p.1.2 = s then ans_v else 0)
    have hih (c₀ ans_v : Bool) := ih hL (acc' c₀ ans_v)
    dsimp only [pairsSteps, pairsSchedule, pairRound, List.map, Round.embed,
      Composition.Steps.embed]
    simp only [runOTSteps, runOTSteps_mapState, runOTSteps_embed_mapState,
      realPairsCalls, realPairCall,
      map_bind, bind_map_left, Functor.map_map, bind_pure_comp, bind_assoc]
    refine congrArg (Bind.bind _) (funext fun c₀ => ?_)
    refine congrArg (Bind.bind _) (funext fun rep => ?_)
    have hst :
        (fun i : Fin m =>
          ((), fun (s : Fin m) (hs : (Function.Embedding.refl (Fin m)) s = i) =>
            (x s,
             acc s +
              extractPairShare p s
                (Composition.pullRoundReceived (Function.Embedding.refl (Fin m)) (pairRound p) hs
                  (Round.deliverOracle (spec := sharedMulSpec 2) (op := ())
                    ((pairEmbedding p).trans (Function.Embedding.refl (Fin m)))
                    (Fin.cases c₀ (fun _ => (List.take 1 rep).headD false)) i))))) =
        fun i : Fin m =>
          ((), fun (s : Fin m) (_ : (Function.Embedding.refl (Fin m)) s = i) =>
            (x s, acc' c₀ ((List.take 1 rep).headD false) s)) := by
      funext i
      refine Prod.ext rfl (funext fun s => funext fun hs => Prod.ext rfl ?_)
      exact congrArg (acc s + ·) (extractPairShare_pullRoundReceived_deliverOracle p c₀
        ((List.take 1 rep).headD false) s i hs)
    rw [hst]
    have hih' := hih c₀ ((List.take 1 rep).headD false)
    have hhead_c (i : Fin m) :
        (if h : ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) 0 = i then
          [Composition.pushTuple ((pairEmbedding p).trans (Function.Embedding.refl (Fin m)))
            (twoPartyMulCoins c₀) i 0 h]
        else []) =
        (if p.1.1 = i then [c₀] else []) := by
      change (if h : p.1.1 = i then [c₀] else []) = (if p.1.1 = i then [c₀] else [])
      split_ifs <;> rfl
    have hhead_a (i : Fin m) :
        (if h : ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) 1 = i then
          [Round.deliverOracle (spec := ot14Spec) (op := ())
            ((Function.Embedding.refl (Fin 2)).trans
              ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))))
            (decodeOT14Reply (List.take 1 rep)) i 1 h]
        else []) =
        (if p.1.2 = i then [(List.take 1 rep).headD false] else []) := by
      change (if h : p.1.2 = i then [(List.take 1 rep).headD false] else []) =
        (if p.1.2 = i then [(List.take 1 rep).headD false] else [])
      split_ifs <;> rfl
    let post (c₀ ans_v : Bool)
        (t : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
        (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool) :=
      (t.1,
       fun i => (if p.1.1 = i then [c₀] else []) ++ t.2.1 i,
       fun i => (if p.1.2 = i then [ans_v] else []) ++ t.2.2 i)
    have hcongr := congrArg (post c₀ ((List.take 1 rep).headD false) <$> ·) hih'
    simp only [Functor.map_map] at hcongr
    refine Eq.trans ?_ (Eq.trans hcongr ?_)
    · refine congrArg (· <$> _) (funext fun res => ?_)
      refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
      · exact congrArg (· ++ _) (hhead_c i)
      · exact congrArg (· ++ _) (hhead_a i)
    · refine congrArg (· <$> _) (funext fun tr => ?_)
      have hmap_sum (i : Fin m) :
          (L.map fun q =>
            if q.1.1 = i then (Function.update tr p (c₀, (List.take 1 rep).headD false) q).1
            else if q.1.2 = i then (Function.update tr p (c₀, (List.take 1 rep).headD false) q).2
            else 0) =
          (L.map fun q =>
            if q.1.1 = i then (tr q).1 else if q.1.2 = i then (tr q).2 else 0) := by
        refine List.map_congr_left fun q hq => ?_
        have hne : q ≠ p := fun h => hp (h ▸ hq)
        simp [Function.update_of_ne hne]
      have hmap_c (i : Fin m) :
          (L.map fun q =>
            if q.1.1 = i then [(Function.update tr p (c₀, (List.take 1 rep).headD false) q).1]
            else []) =
          (L.map fun q => if q.1.1 = i then [(tr q).1] else []) := by
        refine List.map_congr_left fun q hq => ?_
        have hne : q ≠ p := fun h => hp (h ▸ hq)
        simp [Function.update_of_ne hne]
      have hmap_a (i : Fin m) :
          (L.map fun q =>
            if q.1.2 = i then [(Function.update tr p (c₀, (List.take 1 rep).headD false) q).2]
            else []) =
          (L.map fun q => if q.1.2 = i then [(tr q).2] else []) := by
        refine List.map_congr_left fun q hq => ?_
        have hne : q ≠ p := fun h => hp (h ▸ hq)
        simp [Function.update_of_ne hne]
      refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
      · dsimp only [post, acc', List.map_cons, List.sum_cons]
        rw [Function.update_self, hmap_sum, add_assoc]
      · dsimp only [post, List.map_cons, List.flatten_cons]
        rw [Function.update_self, hmap_c]
      · dsimp only [post, List.map_cons, List.flatten_cons]
        rw [Function.update_self, hmap_a]

private theorem runSharedMulSteps_oracle_done {m : ℕ} {S : Type} {Out : Fin m → Type}
    (query : (s : Fin m) → S → Bool × Bool)
    (finish : (i : Fin m) → S → Bool → Out i)
    (st : Fin m → S) :
    ((fun res =>
      (res.2.2,
       fun i =>
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          i (res.2.1 i))) <$>
      runSharedMulSteps (State := fun _ => S)
        (.oracle (spec := sharedMulSpec m) (op := ())
          (parties := Function.Embedding.refl (Fin m))
          query (.done fun i st_i => finish i st_i.1 (st_i.2 i rfl)))
        st) =
    (fun tr =>
      let mul := realSharedMulPure m (fun s => query s (st s)) tr
      (fun i => finish i (st i) (mul.1 i), mul.2.1, mul.2.2)) <$>
      realPairsCalls m (fun s => query s (st s)) (orderedPairs m) := by
  let x : Fin m → Bool × Bool := fun s => query s (st s)
  simp only [runSharedMulSteps, Composition.Steps.compose, unitSubCoins,
    runOTSteps_append, runOTSteps_mapState, multiPartyMulProtocol]
  conv_lhs => arg 2; arg 1; rw [runOTSteps_embed]
  simp only [runOTSteps_embed_mapState, runOTSteps,
    map_pure, bind_pure_comp, Functor.map_map]
  have hrun :
      runOTSteps
        (Composition.Steps.embed (Function.Embedding.refl (Fin m)) (fun _ => Unit)
          (pairsSteps (orderedPairs m)))
        (fun i : Fin m =>
          ((), fun (s : Fin m) (hs : (Function.Embedding.refl (Fin m)) s = i) =>
            (query s (Eq.rec (motive := fun _ _ => S) (st i) hs.symm),
              m • ((query s (Eq.rec (motive := fun _ _ => S) (st i) hs.symm)).1 *
                (query s (Eq.rec (motive := fun _ _ => S) (st i) hs.symm)).2)))) =
      runOTSteps
        (Composition.Steps.embed (Function.Embedding.refl (Fin m)) (fun _ => Unit)
          (pairsSteps (orderedPairs m)))
        (fun i : Fin m =>
          ((), fun (s : Fin m) (_ : (Function.Embedding.refl (Fin m)) s = i) =>
            (x s, m • ((x s).1 * (x s).2)))) := by
    refine congrArg (runOTSteps _) (funext fun i => ?_)
    refine Prod.ext rfl (funext fun s => funext fun hs => ?_)
    change s = i at hs
    subst hs
    rfl
  have hpairs := runOTSteps_embed_pairsSteps x (MultiPartyMul.nodup_orderedPairs m)
    (fun s => m • ((x s).1 * (x s).2))
  let post (t : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
      ((i : Fin m) → Out i) × (Fin m → List Bool) × (Fin m → List Bool) :=
    (fun i => finish i (st i) (t.1 i), t.2.1, t.2.2)
  have hcongr := (congrArg (fun d => post <$> ((fun res =>
      (fun i => (res.2.2 i).2 i rfl,
       fun i =>
        encOTSubCoins
          ((pairsSchedule (orderedPairs m)).map (Round.embed (Function.Embedding.refl (Fin m))))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          ((pairsSchedule (orderedPairs m)).map (Round.embed (Function.Embedding.refl (Fin m))))
          i (res.2.1 i))) <$> d)) hrun).trans (congrArg (post <$> ·) hpairs)
  simp only [Functor.map_map] at hcongr
  refine Eq.trans ?_ hcongr
  refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun res => ?_)
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
  · dsimp only [Schedule.compose, List.append_nil, post]
    rw [encOTSubCoins_joinSubCoins2, encOTSubCoins_nil, List.append_nil]
  · dsimp only [Schedule.compose, List.append_nil, post]
    rw [encOTOracleAnswers_joinReceived2, encOTOracleAnswers_nil, List.append_nil]

private theorem encOT_detExpandOTSim_pairsSchedule {m : ℕ} (I : Finset (Fin m))
    (row : Fin m → Fin m → Bool) (L : List (OrderedPair m)) (i : I) :
    let sc := (pairsSchedule L).map (Round.embed (Function.Embedding.refl (Fin m)))
    let ot := detExpandOTSim I sc
      (Composition.pushScheduleReceivedRestrict (Function.Embedding.refl (Fin m)) I
        (pairsSchedule L)
        (fun s => MultiPartyMul.receivedScheduleOfRow s.1 (row s.1) L)) i
    (encOTSubCoins sc i.1 ot.1, encOTOracleAnswers sc i.1 ot.2) =
      ((L.map fun p => if p.1.1 = i.1 then [row i.1 p.1.2] else []).flatten,
       (L.map fun p => if p.1.2 = i.1 then [row i.1 p.1.1] else []).flatten) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hhead_c :
        (if h : ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) 0 = i.1 then
          [Composition.pushTupleRestrict
            ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) I
            (fun s =>
              twoPartyMulCoins
                (MultiPartyMul.receivedPairOfRow p (pairEmbedding p s.1)
                  (row (pairEmbedding p s.1)) s.1 rfl) s.1)
            i 0 h]
        else []) =
        (if p.1.1 = i.1 then [row i.1 p.1.2] else []) := by
      change (if h : p.1.1 = i.1 then [row p.1.1 p.1.2] else []) =
        (if p.1.1 = i.1 then [row i.1 p.1.2] else [])
      by_cases h : p.1.1 = i.1 <;> simp [h]
    have hhead_a :
        (if h : ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) 1 = i.1 then
          [Composition.pushRoundReceivedRestrict
            ((pairEmbedding p).trans (Function.Embedding.refl (Fin m))) I
            (.oracle (spec := ot14Spec) () (Function.Embedding.refl (Fin 2)))
            (fun s =>
              twoPartyMulReceived s.1
                (MultiPartyMul.receivedPairOfRow p (pairEmbedding p s.1)
                  (row (pairEmbedding p s.1)) s.1 rfl))
            i 1 h]
        else []) =
        (if p.1.2 = i.1 then [row i.1 p.1.1] else []) := by
      change (if h : p.1.2 = i.1 then [row p.1.2 p.1.1] else []) =
        (if p.1.2 = i.1 then [row i.1 p.1.1] else [])
      by_cases h : p.1.2 = i.1 <;> simp [h]
    dsimp only [pairsSchedule, pairRound, List.map, Round.embed,
      MultiPartyMul.receivedScheduleOfRow, Composition.pushScheduleReceivedRestrict,
      detExpandOTSim, encOTSubCoins, encOTOracleAnswers, List.flatten_cons] at ih ⊢
    rw [Prod.mk.injEq] at ih
    refine Prod.ext ?_ ?_
    · rw [← ih.1]
      exact congrArg (· ++ _) hhead_c
    · rw [← ih.2]
      exact congrArg (· ++ _) hhead_a

@[simp] private theorem subCoalition_refl {m : ℕ} (I : Finset (Fin m)) :
    Composition.subCoalition (Function.Embedding.refl (Fin m)) I = I := by
  ext s
  simp [Composition.subCoalition]

@[simp] private theorem freeM_map_eq_map {F : PFunctor} {α β : Type}
    (f : α → β) (x : PFunctor.FreeM F α) :
    PFunctor.FreeM.map f x = f <$> x := rfl

private theorem simSharedMulSteps_oracle_done {m : ℕ} [NeZero m] {S : Type} {Out : Fin m → Type}
    (I : Finset (Fin m))
    (query : (s : Fin m) → S → Bool × Bool)
    (output : (i : Fin m) →
      (S ×
        (Round.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))).Received i) →
      Out i)
    (stI : (i : I) → S)
    (x : Fin m → Bool × Bool) (hx : ∀ i : I, query i.1 (stI i) = x i.1)
    (ans : Fin m → Bool) :
    ((fun res (i : I) =>
      (encOTSubCoins
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
        i.1 (res i).1,
       encOTOracleAnswers
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
        i.1 (res i).2)) <$>
      simSharedMulSteps (State := fun _ => S) I
        (.oracle (spec := sharedMulSpec m) (op := ())
          (parties := Function.Embedding.refl (Fin m))
          query (.done output))
        stI
        (fun i =>
          (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
            (Function.Embedding.refl (Fin m)) ans i.1, ()))) =
    (fun r (i : I) =>
      ((simSharedMulPure m I x ans r).1 i.1,
       (simSharedMulPure m I x ans r).2 i.1)) <$>
      ProbComp.uniform (OrderedPair m → Bool) := by
  let J := Composition.subCoalition (Function.Embedding.refl (Fin m)) I
  have hJ : J = I := subCoalition_refl I
  have hx₀ :
      MultiPartyMul.extendIn J
        (fun s : J =>
          query s.1
            (stI ⟨(Function.Embedding.refl (Fin m)) s.1, Composition.mem_subCoalition.1 s.2⟩)) =
      MultiPartyMul.extendIn I (I.restrict x) := by
    funext j
    by_cases hj : j ∈ I
    · have hjJ : j ∈ J := Composition.mem_subCoalition.2 hj
      simp [MultiPartyMul.extendIn, hj, hjJ, hx ⟨j, hj⟩]
    · have hjJ : j ∉ J := fun h => hj (Composition.mem_subCoalition.1 h)
      simp [MultiPartyMul.extendIn, hj, hjJ]
  have hy₀ :
      MultiPartyMul.extendOut J
        (fun s : J =>
          Round.deliverOracle (spec := sharedMulSpec m) (op := ())
            (Function.Embedding.refl (Fin m)) ans
            ((Function.Embedding.refl (Fin m)) s.1) s.1 rfl) =
      MultiPartyMul.extendOut I (I.restrict ans) := by
    funext j
    by_cases hj : j ∈ I
    · have hjJ : j ∈ J := Composition.mem_subCoalition.2 hj
      simp [MultiPartyMul.extendOut, hj, hjJ, Round.deliverOracle]
    · have hjJ : j ∉ J := fun h => hj (Composition.mem_subCoalition.1 h)
      simp [MultiPartyMul.extendOut, hj, hjJ]
  have hpivot : MultiPartyMul.pivotParty J = MultiPartyMul.pivotParty I :=
    congrArg MultiPartyMul.pivotParty hJ
  rw [simSharedMulSteps_oracle]
  simp only [simSharedMulSteps_done, multiPartyMulSim, freeM_map_eq_map,
    bind_pure_comp, map_pure, Functor.map_map]
  refine congrArg (Functor.map (f := ProbComp) · (ProbComp.uniform (OrderedPair m → Bool)))
    (funext fun r => ?_)
  funext i
  dsimp only [Schedule.compose, List.append_nil, MultiPartyMul.viewOfRow, simSharedMulPure]
  rw [encOTSubCoins_joinSubCoins2, encOTSubCoins_nil, List.append_nil,
    encOTOracleAnswers_joinReceived2, encOTOracleAnswers_nil, List.append_nil,
    hx₀, hy₀, hpivot]
  exact encOT_detExpandOTSim_pairsSchedule I
    (MultiPartyMul.matrixOfCoins (MultiPartyMul.extendIn I (I.restrict x))
      (MultiPartyMul.tildeR (MultiPartyMul.pivotParty I)
        (MultiPartyMul.extendIn I (I.restrict x))
        (MultiPartyMul.extendOut I (I.restrict ans)) r))
    (orderedPairs m) i

/-! #### Sub-part 4C.2: Step 1 (`inputShareSteps`) Equivalence -/

/-- Unit subcoins for party `i` along `GMWCircuit.msgSchedule Msg L` under `otMulCompose`. -/
private def unitOTMsgSubCoins {m : ℕ} {Msg : Type} (i : Fin m) :
    (L : List (Fin m × Fin m)) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)) i
  | [] => ()
  | _ :: L => unitOTMsgSubCoins i L

/-- Received transcript for party `i` along `otMulCompose (GMWCircuit.msgSchedule Msg L)`
constructed from `inbox_i`. -/
private def receivedOTMsgScheduleOfInbox {m : ℕ} {Msg : Type}
    (i : Fin m) (inbox_i : Fin m → Msg) :
    (L : List (Fin m × Fin m)) →
      (otMulCompose (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)).Received i
  | [] => ()
  | p :: L =>
    (GMWCircuit.receivedMsgOfInbox (spec := ot14Spec) p i inbox_i,
     receivedOTMsgScheduleOfInbox i inbox_i L)

@[simp] private theorem encOTSubCoins_msgSchedule {m : ℕ} {Msg : Type}
    (L : List (Fin m × Fin m)) (i : Fin m)
    (c : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)) i) :
    encOTSubCoins
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)) i c = [] := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact ih c

@[simp] private theorem encOTOracleAnswers_msgSchedule {m : ℕ} {Msg : Type}
    (L : List (Fin m × Fin m)) (i : Fin m)
    (r : (otMulCompose (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)).Received i) :
    encOTOracleAnswers
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.msgSchedule (spec := sharedMulSpec m) Msg L)) i r = [] := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact ih r.2

@[simp] private theorem runSharedMulSteps_done {m : ℕ} {State Out : Fin m → Type}
    (output : (i : Fin m) → State i → Out i) (st : (i : Fin m) → State i) :
    runSharedMulSteps (sc := []) (.done output) st =
      pure (fun _ => (), fun _ => (), fun i => output i (st i)) := rfl

@[simp] private theorem runSharedMulSteps_message {m : ℕ} {State Out : Fin m → Type}
    {s₀ r₀ : Fin m} {Msg : Type} {rest : Schedule m (sharedMulSpec m)}
    (send : State s₀ → Msg)
    (next : Steps (fun i => State i × (Round.message s₀ r₀ Msg).Received i) Out rest)
    (st : (i : Fin m) → State i) :
    runSharedMulSteps (.message send next) st = (do
      let r_head :=
        Round.deliverMessage (spec := ot14Spec) (sender := s₀) (receiver := r₀) (send (st s₀))
      let cr_tail ← runSharedMulSteps next (fun i => (st i, r_head i))
      return (cr_tail.1, fun i => (r_head i, cr_tail.2.1 i), cr_tail.2.2)) := by
  simp only [runSharedMulSteps, Composition.Steps.compose, unitSubCoins, runOTSteps,
    runOTSteps_mapState]
  rfl

private theorem runSharedMulSteps_msgStepsWith {m : ℕ} {Msg : Type} [AddCommMonoid Msg]
    {Out : Fin m → Type} (finish : (i : Fin m) → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (st : (i : Fin m) → (Fin m → Msg) × (Fin m → Msg)) :
    runSharedMulSteps (GMWCircuit.msgStepsWith (spec := sharedMulSpec m) finish L) st =
      pure (fun i => unitOTMsgSubCoins i L,
        fun i => receivedOTMsgScheduleOfInbox i (fun s => (st s).1 i) L,
        fun i => (GMWCircuit.msgStepsWith (spec := sharedMulSpec m) finish L).outputAt i (st i)
          (GMWCircuit.receivedScheduleOfInbox (spec := sharedMulSpec m) i
            (fun s => (st s).1 i) L)) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp only [GMWCircuit.msgStepsWith, runSharedMulSteps_message, runSharedMulSteps_mapState,
      ih, pure_bind, GMWCircuit.deliverMessage_eq_receivedMsgOfInbox (fun s => (st s).1) p,
      GMWCircuit.receivedScheduleOfInbox, receivedOTMsgScheduleOfInbox, unitOTMsgSubCoins,
      Steps.outputAt, Steps.outputAt_mapState]
    rfl

private theorem runSharedMulSteps_inputShareSteps {m N : ℕ}
    (xr : Fin m → BitString N) (c : Fin m → Fin N → Fin (m - 1) → Bool) :
    runSharedMulSteps (GMWCircuit.inputShareSteps m N) (fun i => (xr i, c i)) =
      pure (fun i => unitOTMsgSubCoins i (GMWCircuit.allPairs m),
        fun i => receivedOTMsgScheduleOfInbox i
          (fun s => GMWCircuit.shareInputBits m N (xr s) (c s) i) (GMWCircuit.allPairs m),
        fun i => Cslib.BitString.blocksEquiv.symm
          (fun s => GMWCircuit.shareInputBits m N (xr s) (c s) i)) := by
  simp only [GMWCircuit.inputShareSteps, GMWCircuit.allToAllStepsWith,
    runSharedMulSteps_mapState, runSharedMulSteps_msgStepsWith]
  congr 1
  refine Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))
  have hout := GMWCircuit.outputAt_inputShareSteps xr c i
  simpa only [GMWCircuit.inputShareSteps, GMWCircuit.allToAllStepsWith,
    GMWCircuit.deliverInputShares, Steps.outputAt_mapState] using hout

private theorem simSharedMulSteps_msgStepsWith {m : ℕ} [NeZero m] {Msg : Type} [AddCommMonoid Msg]
    {Out : Fin m → Type} (I : Finset (Fin m))
    (finish : (i : Fin m) → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m))
    (stI : (i : I) → (Fin m → Msg) × (Fin m → Msg))
    (inboxI : (i : I) → Fin m → Msg) :
    simSharedMulSteps I (GMWCircuit.msgStepsWith (spec := sharedMulSpec m) finish L) stI
      (fun i => GMWCircuit.receivedScheduleOfInbox (spec := sharedMulSpec m) i.1 (inboxI i) L) =
    pure (fun i =>
      (unitOTMsgSubCoins i.1 L, receivedOTMsgScheduleOfInbox i.1 (inboxI i) L)) := by
  induction L generalizing stI with
  | nil => rfl
  | cons p L ih =>
    simp only [GMWCircuit.msgStepsWith, GMWCircuit.receivedScheduleOfInbox,
      receivedOTMsgScheduleOfInbox, unitOTMsgSubCoins,
      simSharedMulSteps_message, simSharedMulSteps_mapState, ih, map_pure]
    rfl

private theorem simSharedMulSteps_inputShareSteps {m N : ℕ} [NeZero m]
    (I : Finset (Fin m))
    (stI : (i : I) → BitString N × (Fin N → Fin (m - 1) → Bool))
    (inboxI : (i : I) → Fin m → BitString N) :
    simSharedMulSteps I (GMWCircuit.inputShareSteps m N) stI
      (fun i =>
        GMWCircuit.receivedScheduleOfInbox (spec := sharedMulSpec m) i.1 (inboxI i)
          (GMWCircuit.allPairs m)) =
    pure (fun i =>
      (unitOTMsgSubCoins i.1 (GMWCircuit.allPairs m),
       receivedOTMsgScheduleOfInbox i.1 (inboxI i) (GMWCircuit.allPairs m))) := by
  simp only [GMWCircuit.inputShareSteps, GMWCircuit.allToAllStepsWith,
    simSharedMulSteps_mapState, simSharedMulSteps_msgStepsWith]

private theorem encPairsMsgReceived_append_receivedOTMsgScheduleOfInbox {m N : ℕ} (i : Fin m)
    (inbox_i : Fin m → BitString N) (L₁ L₂ : List (Fin m × Fin m)) :
    encPairsMsgReceived i (L₁ ++ L₂)
      (receivedOTMsgScheduleOfInbox i inbox_i (L₁ ++ L₂)) =
    encPairsMsgReceived i L₁
      (receivedOTMsgScheduleOfInbox i inbox_i L₁) ++
    encPairsMsgReceived i L₂
      (receivedOTMsgScheduleOfInbox i inbox_i L₂) := by
  induction L₁ with
  | nil => rfl
  | cons p L₁ ih =>
    simp [receivedOTMsgScheduleOfInbox, encPairsMsgReceived, ih, List.append_assoc]

private theorem encPairsMsgReceived_map_pair {m N : ℕ} (i s : Fin m)
    (inbox_i : Fin m → BitString N) (R : List (Fin m)) :
    encPairsMsgReceived i (R.map fun r => (s, r))
      (receivedOTMsgScheduleOfInbox i inbox_i (R.map fun r => (s, r))) =
    (R.map fun r => if i = r then List.ofFn (inbox_i s) else []).flatten := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    change
      (if h : i = r then List.ofFn (GMWCircuit.receivedMsgOfInbox (s, r) i inbox_i h) else []) ++
        encPairsMsgReceived i (R.map fun r => (s, r))
          (receivedOTMsgScheduleOfInbox i inbox_i (R.map fun r => (s, r))) =
      (if i = r then List.ofFn (inbox_i s) else []) ++
        (R.map fun r => if i = r then List.ofFn (inbox_i s) else []).flatten
    rw [ih]
    by_cases h : i = r <;> simp [h, GMWCircuit.receivedMsgOfInbox]

private theorem flatten_map_ite_eq {α : Type} [DecidableEq α] (i : α) (val : List Bool) :
    ∀ {R : List α}, R.Nodup →
      ((R.map fun r => if i = r then val else []).flatten =
        if i ∈ R then val else [])
  | [], _ => rfl
  | r :: R, hnodup => by
    obtain ⟨hr, hR⟩ := List.nodup_cons.mp hnodup
    have ih := flatten_map_ite_eq i val hR
    simp only [List.map_cons, List.flatten_cons, List.mem_cons, ih]
    by_cases hir : i = r
    · subst hir
      simp [hr]
    · simp [hir]

private theorem encPairsMsgReceived_allPairs {m N : ℕ} (i : Fin m)
    (inbox_i : Fin m → BitString N) :
    encPairsMsgReceived i (GMWCircuit.allPairs m)
      (receivedOTMsgScheduleOfInbox i inbox_i (GMWCircuit.allPairs m)) =
    List.ofFn (Cslib.BitString.blocksEquiv.symm inbox_i) := by
  have hS : ∀ S : List (Fin m),
      encPairsMsgReceived i (S.flatMap fun s => (List.finRange m).map fun r => (s, r))
        (receivedOTMsgScheduleOfInbox i inbox_i
          (S.flatMap fun s => (List.finRange m).map fun r => (s, r))) =
      (S.map fun s => List.ofFn (inbox_i s)).flatten := by
    intro S
    induction S with
    | nil => rfl
    | cons s S ih =>
      change encPairsMsgReceived i
          (((List.finRange m).map fun r => (s, r)) ++
            (S.flatMap fun s => (List.finRange m).map fun r => (s, r)))
          (receivedOTMsgScheduleOfInbox i inbox_i
            (((List.finRange m).map fun r => (s, r)) ++
              (S.flatMap fun s => (List.finRange m).map fun r => (s, r)))) =
        List.ofFn (inbox_i s) ++ (S.map fun s => List.ofFn (inbox_i s)).flatten
      rw [encPairsMsgReceived_append_receivedOTMsgScheduleOfInbox, ih,
        encPairsMsgReceived_map_pair,
        flatten_map_ite_eq i (List.ofFn (inbox_i s)) (List.nodup_finRange m)]
      simp [List.mem_finRange]
  rw [GMWCircuit.allPairs, hS, Cslib.BitString.ofFn_blocksEquiv_symm, List.ofFn_eq_map]

private theorem step1SenderShare_ofFn {m N : ℕ} (xr_s : BitString N)
    (c_s : Fin N → Fin (m - 1) → Bool) (i : Fin m) :
    step1SenderShare m N (List.ofFn xr_s)
      (List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm c_s)) i =
    List.ofFn (GMWCircuit.shareInputBits m N xr_s c_s i) := by
  refine List.ext_getElem (by simp [step1SenderShare]) fun j hj₁ hj₂ => ?_
  have hjN : j < N := by simpa [step1SenderShare] using hj₁
  let jFin : Fin N := ⟨j, hjN⟩
  have hbit : (List.ofFn xr_s).getD j false = xr_s jFin := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hjN),
      Option.getD_some, List.getElem_ofFn]
  have hrow :
      Cslib.BitString.ofList (m - 1)
        (Cslib.BitString.listRow (m - 1) j
          (List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm c_s))) =
      c_s jFin := by
    have hj_eq : j = jFin.val := rfl
    rw [hj_eq, Cslib.BitString.listRow_eq_ofFn (m - 1) jFin]
    simp
  simp only [step1SenderShare, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    GMWCircuit.shareInputBits_apply, hbit, hrow]
  rfl

private theorem ofFn_fin_append {n₁ n₂ : ℕ} (u : BitString n₁) (v : BitString n₂) :
    List.ofFn (Fin.append u v) = List.ofFn u ++ List.ofFn v := by
  rw [List.ofFn_add]
  simp [Fin.append_right]

private theorem step1Wires_ofFn {m n coins : ℕ}
    (x : Fin m → BitString n) (r : Fin m → BitString coins)
    (c : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) (i : Fin m) :
    step1Wires m (n + coins)
      (fun s => List.ofFn (x s))
      (fun s => List.ofFn (r s))
      (fun s =>
        List.ofFn
          ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c s)))
      i =
    List.ofFn (Cslib.BitString.blocksEquiv.symm
      (fun s => GMWCircuit.shareInputBits m (n + coins) (Fin.append (x s) (r s)) (c s) i)) := by
  dsimp only [step1Wires]
  rw [Cslib.BitString.ofFn_blocksEquiv_symm, List.ofFn_eq_map, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun s _ => ?_)
  rw [← ofFn_fin_append (x s) (r s), step1SenderShare_ofFn]

/-! #### Sub-part 4C.3: Step 2 (`progSteps`) Equivalence -/

/-- Serialize a party's wire valuation `w : Wire n g → Bool` into a list of `n + g` bits
(input wires followed by gate wires). -/
private def wireToList {n g : ℕ} (w : Wire n g → Bool) : List Bool :=
  List.ofFn (fun j : Fin n => w (.input j)) ++ List.ofFn (fun j : Fin g => w (.gate j))

@[simp] private theorem wireToList_elim_elim0 {n : ℕ} (x_in : Fin n → Bool) :
    wireToList (Wire.elim x_in Fin.elim0) = List.ofFn x_in := by
  simp [wireToList]

@[simp] private theorem extendWire_input {n g : ℕ} (lastBit : Bool)
    (w : Wire n g → Bool) (j : Fin n) :
    GMWCircuit.extendWire lastBit w (.input j) = w (.input j) :=
  GMWCircuit.extendWire_castSucc lastBit w (.input j)

@[simp] private theorem extendWire_gate_castSucc {n g : ℕ} (lastBit : Bool)
    (w : Wire n g → Bool) (j : Fin g) :
    GMWCircuit.extendWire lastBit w (.gate j.castSucc) = w (.gate j) :=
  GMWCircuit.extendWire_castSucc lastBit w (.gate j)

@[simp] private theorem wireToList_extendWire {n g : ℕ} (lastBit : Bool) (w : Wire n g → Bool) :
    wireToList (GMWCircuit.extendWire lastBit w) = wireToList w ++ [lastBit] := by
  simp only [wireToList, List.ofFn_succ' (fun j => GMWCircuit.extendWire lastBit w (.gate j)),
    List.concat_eq_append, List.append_assoc,
    extendWire_input, extendWire_gate_castSucc, GMWCircuit.extendWire_last]

private theorem getD_wireToList_toNat {n g : ℕ} (w : Wire n g → Bool) (wire : Wire n g) :
    (wireToList w).getD wire.toNat false = w wire := by
  rw [wireToList, Wire.getD_append_toNat]
  cases wire <;> rfl

private theorem extractGateCoreInput_not {m n g : ℕ}
    (wires : Fin (Boolean.signature.Arity Boolean.Op.not) → Wire n g)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    (extractGateCoreInput m
      (Line.code (σ := Boolean.signature) ⟨.not, wires⟩,
        (fun i => wireToList (w i), c, a))).1 = Boolean.Op.not ∧
    ∀ s : Fin m,
      ((extractGateCoreInput m
        (Line.code (σ := Boolean.signature) ⟨.not, wires⟩,
          (fun i => wireToList (w i), c, a))).2 s).1 = w s (wires 0) := by
  refine ⟨rfl, fun s => ?_⟩
  change (wireToList (w s)).getD (wires 0).toNat false = w s (wires 0)
  exact getD_wireToList_toNat (w s) (wires 0)

private theorem extractGateCoreInput_and {m n g : ℕ}
    (wires : Fin (Boolean.signature.Arity Boolean.Op.and) → Wire n g)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    extractGateCoreInput m
      (Line.code (σ := Boolean.signature) ⟨.and, wires⟩, (fun i => wireToList (w i), c, a)) =
      (.and, fun s => (w s (wires 0), w s (wires 1))) := by
  refine Prod.ext rfl (funext fun s => Prod.ext ?_ ?_)
  · change (wireToList (w s)).getD (wires 0).toNat false = w s (wires 0)
    exact getD_wireToList_toNat (w s) (wires 0)
  · change (wireToList (w s)).getD (wires 1).toNat false = w s (wires 1)
    exact getD_wireToList_toNat (w s) (wires 1)

private theorem extractGateCoreInput_or {m n g : ℕ}
    (wires : Fin (Boolean.signature.Arity Boolean.Op.or) → Wire n g)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    extractGateCoreInput m
      (Line.code (σ := Boolean.signature) ⟨.or, wires⟩, (fun i => wireToList (w i), c, a)) =
      (.or, fun s => (w s (wires 0), w s (wires 1))) := by
  refine Prod.ext rfl (funext fun s => Prod.ext ?_ ?_)
  · change (wireToList (w s)).getD (wires 0).toNat false = w s (wires 0)
    exact getD_wireToList_toNat (w s) (wires 0)
  · change (wireToList (w s)).getD (wires 1).toNat false = w s (wires 1)
    exact getD_wireToList_toNat (w s) (wires 1)

/-- Pack the output of `runSharedMulSteps` on a Step 2 schedule into `Step2Acc m`. -/
private def packStep2 {m n g : ℕ} {sc : Schedule m (sharedMulSpec m)}
    (res : ((i : Fin m) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m) sc) i) ×
      ((i : Fin m) → (otMulCompose sc).Received i) ×
      ((i : Fin m) → Wire n g → Bool)) : Step2Acc m :=
  (fun i => wireToList (res.2.2 i),
   fun i => encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m) sc) i (res.1 i),
   fun i =>
     encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m) sc) i (res.2.1 i))

private theorem runSharedMulSteps_lineSteps {m n g : ℕ} [NeZero m]
    (line : Line Boolean.signature n g)
    (w : Fin m → Wire n g → Bool) (c₁ a₁ : Fin m → List Bool) :
    ((fun res₂ =>
      (fun i => wireToList (res₂.2.2 i),
       fun i => c₁ i ++
         encOTSubCoins
           (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.lineSchedule m line))
           i (res₂.1 i),
       fun i => a₁ i ++
         encOTOracleAnswers
           (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.lineSchedule m line))
           i (res₂.2.1 i))) <$>
      runSharedMulSteps (GMWCircuit.lineSteps m line) w) =
    realGateStep m line.code (fun i => wireToList (w i), c₁, a₁) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | const b =>
    simp [GMWCircuit.lineSteps, GMWCircuit.lineSchedule, realGateStep, realGateCore,
      extractGateCoreInput, Line.code, appendStep2Acc, encOTSubCoins_nil, encOTOracleAnswers_nil]
  | not =>
    obtain ⟨h1, h2⟩ := extractGateCoreInput_not wires w c₁ a₁
    simp only [GMWCircuit.lineSteps, GMWCircuit.lineSchedule, runSharedMulSteps_done,
      map_pure, wireToList_extendWire, encOTSubCoins_nil, encOTOracleAnswers_nil,
      List.append_nil, realGateStep, realGateCore, h1, h2, appendStep2Acc]
  | and =>
    have hmul := runSharedMulSteps_oracle_done
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ w_i bit => GMWCircuit.extendWire bit w_i) w
    have hcongr := congrArg (Functor.map (f := WordOracleComp Unit)
      (fun t : ((Fin m → Wire n (g + 1) → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun i => wireToList (t.1 i),
         fun i => c₁ i ++ t.2.1 i,
         fun i => a₁ i ++ t.2.2 i))) hmul
    simp only [Functor.map_map] at hcongr
    dsimp only [GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    rw [hcongr, realGateStep, extractGateCoreInput_and, realGateCore, Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
    simp [finishMulGate, appendStep2Acc]
  | or =>
    have hmul := runSharedMulSteps_oracle_done
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ w_i bit => GMWCircuit.extendWire (w_i (wires 0) + w_i (wires 1) + bit) w_i) w
    have hcongr := congrArg (Functor.map (f := WordOracleComp Unit)
      (fun t : ((Fin m → Wire n (g + 1) → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun i => wireToList (t.1 i),
         fun i => c₁ i ++ t.2.1 i,
         fun i => a₁ i ++ t.2.2 i))) hmul
    simp only [Functor.map_map] at hcongr
    dsimp only [GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    rw [hcongr, realGateStep, extractGateCoreInput_or, realGateCore, Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
    simp [finishMulGate, appendStep2Acc]

private theorem runSharedMulSteps_progSteps {m n g : ℕ} [NeZero m]
    (prog : Program Boolean.signature n g)
    (st : Fin m → Fin n → Bool) :
    packStep2 <$> runSharedMulSteps (GMWCircuit.progSteps m prog) st =
      foldlMList (realGateStep m) prog.code
        (fun i => List.ofFn (st i), fun _ => [], fun _ => []) := by
  induction prog with
  | empty =>
    simp [GMWCircuit.progSteps, GMWCircuit.progSchedule, packStep2,
      encOTSubCoins_nil, encOTOracleAnswers_nil]
  | gate p line ih =>
    rw [GMWCircuit.progSteps, Program.code_gate, foldlMList_append, ← ih]
    simp only [runSharedMulSteps_append, map_bind, bind_map_left, bind_pure_comp,
      foldlMList_cons, foldlMList_nil, bind_pure, Functor.map_map]
    refine congrArg (Bind.bind _) (funext fun res₁ => ?_)
    dsimp only [packStep2]
    rw [← runSharedMulSteps_lineSteps line res₁.2.2
      (fun i => encOTSubCoins _ i (res₁.1 i))
      (fun i => encOTOracleAnswers _ i (res₁.2.1 i))]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun res₂ => ?_)
    dsimp only [GMWCircuit.progSchedule]
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · exact encOTSubCoins_joinOTSubCoins (GMWCircuit.progSchedule m p)
        (GMWCircuit.lineSchedule m line) i (res₁.1 i) (res₂.1 i)
    · exact encOTOracleAnswers_joinOTMulCompose (GMWCircuit.progSchedule m p)
        (GMWCircuit.lineSchedule m line) i (res₁.2.1 i) (res₂.2.1 i)

/-- Project `acc : Step2Acc m` to all parties' wire lists and the coalition `I`'s $\text{OT}_1^4$
subcoins and oracle answers. -/
private def projStep2Acc {m : ℕ} (I : Finset (Fin m)) (acc : Step2Acc m) :
    (Fin m → List Bool) × ((i : I) → List Bool) × ((i : I) → List Bool) :=
  (acc.1, I.restrict acc.2.1, I.restrict acc.2.2)

/-- Projected single-gate transition on `projStep2Acc I acc`. -/
private noncomputable def simGateStepProj (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ)
    (accI : (Fin m → List Bool) × ((i : I) → List Bool) × ((i : I) → List Bool)) :
    ProbComp ((Fin m → List Bool) × ((i : I) → List Bool) × ((i : I) → List Bool)) :=
  (fun delta =>
    (fun i => accI.1 i ++ delta.1 i,
     fun i : I => accI.2.1 i ++ delta.2.1 i.1,
     fun i : I => accI.2.2 i ++ delta.2.2 i.1)) <$>
    simGateCore m I (extractGateCoreInput m (gate, (accI.1, fun _ => [], fun _ => [])))

private theorem map_projStep2Acc_simGateStep {m : ℕ} [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ) (acc : Step2Acc m) :
    projStep2Acc I <$> simGateStep m I gate acc =
      simGateStepProj m I gate (projStep2Acc I acc) := by
  simp only [simGateStep, simGateStepProj, Functor.map_map]
  rfl

private theorem simSharedMulSteps_lineSteps {m n g : ℕ} [NeZero m] (I : Finset (Fin m))
    (x_flat : Fin n → Bool) (p : Program Boolean.signature n g)
    (line : Line Boolean.signature n g)
    (w : Fin m → Wire n g → Bool)
    (hw : ∀ wire : Wire n g,
      (∑ i : Fin m, w i wire) = p.trace Boolean.interpretation x_flat wire)
    (cI aI : (i : I) → List Bool) :
    (do
      let r_line ← GMWCircuit.lineDist m x_flat p line
      let sub₂ ←
        simSharedMulSteps I (GMWCircuit.lineSteps m line) (I.restrict w) (I.restrict r_line)
      return (
        fun i : Fin m => wireToList ((GMWCircuit.lineSteps m line).outputAt i (w i) (r_line i)),
        fun i : I => cI i ++
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.lineSchedule m line))
            i.1 (sub₂ i).1,
        fun i : I => aI i ++
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.lineSchedule m line))
            i.1 (sub₂ i).2)) =
    simGateStepProj m I line.code (fun i => wireToList (w i), cI, aI) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | const b =>
    simp [GMWCircuit.lineDist, GMWCircuit.lineSteps, GMWCircuit.lineSchedule,
      Steps.outputAt, encOTSubCoins_nil, encOTOracleAnswers_nil,
      simGateStepProj, simGateCore, extractGateCoreInput, Line.code]
  | not =>
    obtain ⟨h1, h2⟩ := extractGateCoreInput_not wires w (fun _ => []) (fun _ => [])
    simp only [GMWCircuit.lineDist, GMWCircuit.lineSteps, GMWCircuit.lineSchedule,
      Steps.outputAt, simSharedMulSteps_done, pure_bind, map_pure,
      wireToList_extendWire, encOTSubCoins_nil, encOTOracleAnswers_nil, List.append_nil,
      simGateStepProj, simGateCore, h1, h2]
  | and =>
    have hmul (ans : Fin m → Bool) := simSharedMulSteps_oracle_done I
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ st_i => GMWCircuit.extendWire (st_i.2 _ rfl) st_i.1)
      (I.restrict w)
      (fun s => (w s (wires 0), w s (wires 1)))
      (fun _ => rfl) ans
    dsimp only [GMWCircuit.lineDist, GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    rw [← hw (wires 0), ← hw (wires 1), simGateStepProj, extractGateCoreInput_and, simGateCore]
    simp only [bind_map_left, map_bind, bind_pure_comp, Functor.map_map]
    refine congrArg (Bind.bind _) (funext fun ans => ?_)
    have hcongr := congrArg (Functor.map (f := ProbComp)
      (fun (pair : (i : I) → List Bool × List Bool) =>
        (fun i : Fin m => wireToList (w i) ++ [ans i],
         fun i : I => cI i ++ (pair i).1,
         fun i : I => aI i ++ (pair i).2))) (hmul ans)
    simp only [Functor.map_map] at hcongr
    refine Eq.trans ?_ hcongr
    simp [Steps.outputAt, GMWCircuit.deliverMulOracle, Round.deliverOracle, I.restrict_def]
  | or =>
    have hmul (ans : Fin m → Bool) := simSharedMulSteps_oracle_done I
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ st_i =>
        GMWCircuit.extendWire (st_i.1 (wires 0) + st_i.1 (wires 1) + st_i.2 _ rfl) st_i.1)
      (I.restrict w)
      (fun s => (w s (wires 0), w s (wires 1)))
      (fun _ => rfl) ans
    dsimp only [GMWCircuit.lineDist, GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    rw [← hw (wires 0), ← hw (wires 1), simGateStepProj, extractGateCoreInput_or, simGateCore]
    simp only [bind_map_left, map_bind, bind_pure_comp, Functor.map_map]
    refine congrArg (Bind.bind _) (funext fun ans => ?_)
    have hcongr := congrArg (Functor.map (f := ProbComp)
      (fun (pair : (i : I) → List Bool × List Bool) =>
        (fun i : Fin m =>
          wireToList (w i) ++ [w i (wires 0) + w i (wires 1) + ans i],
         fun i : I => cI i ++ (pair i).1,
         fun i : I => aI i ++ (pair i).2))) (hmul ans)
    simp only [Functor.map_map] at hcongr
    refine Eq.trans ?_ hcongr
    simp [Steps.outputAt, GMWCircuit.deliverMulOracle, Round.deliverOracle, I.restrict_def]

private theorem eval_simSharedMulSteps_progSteps {m n g : ℕ} [NeZero m] (I : Finset (Fin m))
    (x_flat : Fin n → Bool) (prog : Program Boolean.signature n g)
    (st : Fin m → Fin n → Bool)
    (hst : ∀ idx : Fin n, (∑ i : Fin m, st i idx) = x_flat idx) :
    ProbComp.eval (do
      let r_prog ← GMWCircuit.progDist m x_flat prog
      let sub ←
        simSharedMulSteps I (GMWCircuit.progSteps m prog) (I.restrict st) (I.restrict r_prog)
      return (
        fun i : Fin m => wireToList ((GMWCircuit.progSteps m prog).outputAt i (st i) (r_prog i)),
        fun i : I =>
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.progSchedule m prog))
            i.1 (sub i).1,
        fun i : I =>
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.progSchedule m prog))
            i.1 (sub i).2)) =
    ProbComp.eval (projStep2Acc I <$>
      foldlMList (simGateStep m I) prog.code
        (fun i => List.ofFn (st i), fun _ => [], fun _ => [])) := by
  induction prog with
  | empty =>
    simp [GMWCircuit.progDist, GMWCircuit.progSteps, GMWCircuit.progSchedule,
      Steps.outputAt, encOTSubCoins_nil, encOTOracleAnswers_nil, projStep2Acc, I.restrict_def]
  | gate p line ih =>
    have hsum_p := (GMWCircuit.evalWith_progSteps x_flat p st hst).2
    rw [Program.code_gate, foldlMList_append]
    simp only [foldlMList_cons, foldlMList_nil, bind_pure, map_bind,
      map_projStep2Acc_simGateStep]
    have hbind :
        ProbComp.eval (do
          let acc ← foldlMList (simGateStep m I) p.code
            (fun i => List.ofFn (st i), fun _ => [], fun _ => [])
          simGateStepProj m I line.code (projStep2Acc I acc)) =
        (ProbComp.eval (projStep2Acc I <$>
          foldlMList (simGateStep m I) p.code
            (fun i => List.ofFn (st i), fun _ => [], fun _ => []))).bind
          (fun accI => ProbComp.eval (simGateStepProj m I line.code accI)) := by
      simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
      rfl
    rw [hbind, ← ih]
    simp only [GMWCircuit.progDist, GMWCircuit.progSteps, GMWCircuit.progSchedule,
      I.restrict_def, simSharedMulSteps_append, Steps.outputAt_append,
      ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
      PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r_p hr_p => ?_
    have hw := hsum_p r_p hr_p
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind (ProbComp.eval (simSharedMulSteps I (GMWCircuit.progSteps m p)
      (I.restrict st) (I.restrict r_p)))) (funext fun sub₁ => ?_)
    rw [← simSharedMulSteps_lineSteps I x_flat p line
      (fun i => (GMWCircuit.progSteps m p).outputAt i (st i) (r_p i)) hw
      (fun i => encOTSubCoins _ i.1 (sub₁ i).1)
      (fun i => encOTOracleAnswers _ i.1 (sub₁ i).2)]
    simp only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp, I.restrict_def]
    refine congrArg (PMF.bind (ProbComp.eval (GMWCircuit.lineDist m x_flat p line)))
      (funext fun r_line => ?_)
    refine congrArg (PMF.map · _) (funext fun sub₂ => ?_)
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · exact encOTSubCoins_joinOTSubCoins (GMWCircuit.progSchedule m p)
        (GMWCircuit.lineSchedule m line) i.1 (sub₁ i).1 (sub₂ i).1
    · exact encOTOracleAnswers_joinOTMulCompose (GMWCircuit.progSchedule m p)
        (GMWCircuit.lineSchedule m line) i.1 (sub₁ i).2 (sub₂ i).2

/-! #### Sub-part 4C.4: Step 3 (`outputSteps`) Equivalence -/

/-- Unit subcoins for party `i` along `GMWCircuit.gatherSchedule m r S` under `otMulCompose`. -/
private def unitOTGatherSubCoins {m : ℕ} (r i : Fin m) :
    (S : List (Fin m)) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i
  | [] => ()
  | _ :: S => unitOTGatherSubCoins r i S

/-- Received transcript for party `i` along `otMulCompose (GMWCircuit.gatherSchedule m r S)`
when sender `s` sends `ans s`. -/
private def deliverOTGather {m : ℕ} (r : Fin m) (ans : Fin m → Bool) :
    (S : List (Fin m)) → (i : Fin m) →
      (otMulCompose (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)).Received i
  | [], _ => ()
  | s :: S, i =>
    (Round.deliverMessage (spec := ot14Spec) (sender := s) (receiver := r) (ans s) i,
     deliverOTGather r ans S i)

@[simp] private theorem encOTSubCoins_gatherSchedule {m : ℕ} (r : Fin m)
    (S : List (Fin m)) (i : Fin m)
    (c : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i) :
    encOTSubCoins
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i c = [] := by
  induction S with
  | nil => rfl
  | cons _ _ ih => exact ih c

@[simp] private theorem encOTOracleAnswers_gatherSchedule {m : ℕ} (r : Fin m)
    (S : List (Fin m)) (i : Fin m)
    (recv : (otMulCompose (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)).Received i) :
    encOTOracleAnswers
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i recv = [] := by
  induction S with
  | nil => rfl
  | cons _ _ ih => exact ih recv.2

private theorem encGatherOTReceived_deliverOTGather {m : ℕ} (r i : Fin m)
    (ans : Fin m → Bool) (S : List (Fin m)) :
    encGatherOTReceived r i S (deliverOTGather r ans S i) =
      if i = r then S.map ans else [] := by
  induction S with
  | nil => simp [encGatherOTReceived, deliverOTGather]
  | cons s S ih =>
    change (if h : i = r then [Round.deliverMessage (spec := ot14Spec) (ans s) i h] else []) ++
        encGatherOTReceived r i S (deliverOTGather r ans S i) =
      if i = r then ans s :: S.map ans else []
    rw [ih]
    by_cases h : i = r <;> simp [h, Round.deliverMessage]

@[simp] private theorem encGatherOTReceived_deliverOTGather_finRange {m : ℕ} (r i : Fin m)
    (ans : Fin m → Bool) :
    encGatherOTReceived r i (List.finRange m) (deliverOTGather r ans (List.finRange m) i) =
      if i = r then List.ofFn ans else [] := by
  rw [encGatherOTReceived_deliverOTGather, List.ofFn_eq_map]

private theorem runSharedMulSteps_gatherStepsWith {m : ℕ} {State Out : Fin m → Type}
    (r : Fin m) (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (st : (i : Fin m) → State i × Bool × Bool) :
    runSharedMulSteps (GMWCircuit.gatherStepsWith (spec := sharedMulSpec m) r finish S) st =
      pure (fun i => unitOTGatherSubCoins r i S,
        fun i => deliverOTGather r (fun s => (st s).2.1) S i,
        fun i => finish i (st i).1
          ((st i).2.2 +
            GMWCircuit.sumGatherBits (spec := sharedMulSpec m) r S i
              (GMWCircuit.deliverGather (spec := sharedMulSpec m) r
                (fun s => (st s).2.1) S i))) := by
  induction S generalizing st with
  | nil =>
    simp [GMWCircuit.gatherStepsWith, GMWCircuit.sumGatherBits,
      unitOTGatherSubCoins, deliverOTGather]
  | cons s S ih =>
    simp only [GMWCircuit.gatherStepsWith, runSharedMulSteps_message, runSharedMulSteps_mapState,
      ih, pure_bind, unitOTGatherSubCoins, deliverOTGather,
      GMWCircuit.sumGatherBits, GMWCircuit.deliverGather, add_assoc]
    rfl

private theorem simSharedMulSteps_gatherStepsWith {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    (I : Finset (Fin m)) (r : Fin m) (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (stI : (i : I) → State i.1 × Bool × Bool)
    (ans : Fin m → Bool) :
    simSharedMulSteps I (GMWCircuit.gatherStepsWith (spec := sharedMulSpec m) r finish S) stI
      (fun i => GMWCircuit.deliverGather (spec := sharedMulSpec m) r ans S i.1) =
    pure (fun i : I =>
      (unitOTGatherSubCoins r i.1 S, deliverOTGather r ans S i.1)) := by
  induction S generalizing stI with
  | nil => rfl
  | cons s S ih =>
    simp only [GMWCircuit.gatherStepsWith, GMWCircuit.deliverGather,
      unitOTGatherSubCoins, deliverOTGather,
      simSharedMulSteps_message, simSharedMulSteps_mapState, ih, map_pure]
    rfl

private theorem singleCoordSteps_eq_append {m k : ℕ} [NeZero m] (coord : Fin m × Fin k) :
    GMWCircuit.singleCoordSteps m k coord =
      (Steps.oracle (spec := sharedMulSpec m)
        (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
        (op := ()) (parties := Function.Embedding.refl (Fin m))
        (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
        (.done fun i st => (st.1, st.2 i rfl, (0 : Bool)))).append
      (GMWCircuit.gatherStepsWith coord.1
        (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
          (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
        (List.finRange m)) := rfl

/-- Identity element of `appendStep3Acc m`. -/
private def zeroStep3Acc (m : ℕ) : Step3Acc m :=
  (fun _ => [], fun _ => [], fun _ => [], fun _ => [])

@[simp] private theorem appendStep3Acc_zero_left {m : ℕ} (acc : Step3Acc m) :
    appendStep3Acc m (zeroStep3Acc m) acc = acc := by
  rcases acc with ⟨c, a, msg, y⟩
  rfl

@[simp] private theorem appendStep3Acc_zero_right {m : ℕ} (acc : Step3Acc m) :
    appendStep3Acc m acc (zeroStep3Acc m) = acc := by
  rcases acc with ⟨c, a, msg, y⟩
  simp [appendStep3Acc, zeroStep3Acc]

private theorem appendStep3Acc_assoc {m : ℕ} (a b c : Step3Acc m) :
    appendStep3Acc m (appendStep3Acc m a b) c =
      appendStep3Acc m a (appendStep3Acc m b c) := by
  simp [appendStep3Acc, List.append_assoc]

private theorem foldlMList_realOutStep_eq_map {m : ℕ} [NeZero m]
    (items : List (OutItem m)) (acc : Step3Acc m) :
    foldlMList (realOutStep m) items acc =
      appendStep3Acc m acc <$> foldlMList (realOutStep m) items (zeroStep3Acc m) := by
  induction items generalizing acc with
  | nil =>
    simp [foldlMList]
  | cons item rest ih =>
    simp only [foldlMList_cons, realOutStep, map_bind, bind_map_left, appendStep3Acc_zero_left]
    refine congrArg (Bind.bind (realOutCore m item)) (funext fun delta => ?_)
    rw [ih (appendStep3Acc m acc delta), ih delta, Functor.map_map]
    exact congrArg (· <$> _) (funext fun a => appendStep3Acc_assoc acc delta a)

private theorem foldlMList_simOutStep_eq_map {m : ℕ} [NeZero m] (I : Finset (Fin m))
    (items : List (OutItem m)) (acc : Step3Acc m) :
    foldlMList (simOutStep m I) items acc =
      appendStep3Acc m acc <$> foldlMList (simOutStep m I) items (zeroStep3Acc m) := by
  induction items generalizing acc with
  | nil =>
    simp [foldlMList]
  | cons item rest ih =>
    simp only [foldlMList_cons, simOutStep, map_bind, bind_map_left, appendStep3Acc_zero_left]
    refine congrArg (Bind.bind (simOutCore m I item)) (funext fun delta => ?_)
    rw [ih (appendStep3Acc m acc delta), ih delta, Functor.map_map]
    exact congrArg (· <$> _) (funext fun a => appendStep3Acc_assoc acc delta a)

/-- Convert a list `L : List (Fin m × Fin k)` of output coordinates into `List (OutItem m)`. -/
private def itemsOfCoords {m k : ℕ} (I : Finset (Fin m))
    (a_table : Fin m → Fin m → BitString k) (y : Fin m → BitString k)
    (L : List (Fin m × Fin k)) : List (OutItem m) :=
  L.map fun coord =>
    (coord.1,
     fun s => a_table s coord.1 coord.2,
     if coord.1 ∈ I then y coord.1 coord.2 else false)

private theorem buildOutItems_eq_itemsOfCoords {m n k : ℕ} (I : Finset (Fin m))
    (D : Circuit Boolean.signature n (m * k))
    (w : Fin m → Wire n D.size → Bool) (y : Fin m → BitString k) :
    buildOutItems m k I D.code.2 (fun s => wireToList (w s)) (fun r => List.ofFn (y r)) =
      itemsOfCoords I
        (fun s r j => w s (D.outputs (finProdFinEquiv (r, j))))
        y (GMWCircuit.outCoords m k) := by
  dsimp only [buildOutItems, itemsOfCoords, GMWCircuit.outCoords]
  rw [List.map_flatMap]
  refine List.flatMap_congr fun r _ => ?_
  have hrange : List.range k = (List.finRange k).map Fin.val :=
    List.ext_getElem (by simp) fun j hj₁ hj₂ => by simp
  rw [hrange, List.map_map, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  dsimp only [Function.comp_def]
  have hidx : r.val * k + j.val = (finProdFinEquiv (r, j)).val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hcode : D.code.2.getD (r.val * k + j.val) 0 =
      (D.outputs (finProdFinEquiv (r, j))).toNat := by
    rw [hidx]
    simp only [Circuit.code, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Fin.is_lt, ↓reduceDIte, Option.getD_some, Fin.eta]
  have hy : (List.ofFn (y r)).getD j.val false = y r j := by
    simp [List.getD_eq_getElem?_getD]
  simp only [hcode, getD_wireToList_toNat, hy]

/-- Pack per-party output bit lists `y_list : Fin m → List Bool` along `L : List (Fin m × Fin k)`
into `Fin m → BitString k`. -/
private def listToBitString {m k : ℕ} :
    (L : List (Fin m × Fin k)) → (Fin m → List Bool) → Fin m → BitString k
  | [], _ => 0
  | coord :: L, y_list =>
    (fun i => if i = coord.1 then Pi.single coord.2 ((y_list i).headD false) else 0) +
      listToBitString L (fun i => if i = coord.1 then (y_list i).tail else y_list i)

/-- Extract party `i`'s output bits along `L : List (Fin m × Fin k)` from
`y_out : Fin m → BitString k`. -/
private def extractOutBits {m k : ℕ} (L : List (Fin m × Fin k)) (y_out : Fin m → BitString k)
    (i : Fin m) : List Bool :=
  (L.map fun coord => if i = coord.1 then [y_out coord.1 coord.2] else []).flatten

private theorem listToBitString_cons {m k : ℕ} (coord : Fin m × Fin k)
    (L : List (Fin m × Fin k)) (b : Bool) (y_tail : Fin m → List Bool) :
    listToBitString (coord :: L)
      (fun i => (if i = coord.1 then [b] else []) ++ y_tail i) =
    (fun i => if i = coord.1 then Pi.single coord.2 b else 0) +
      listToBitString L y_tail := by
  have htail :
      (fun i =>
        if i = coord.1 then ((if i = coord.1 then [b] else []) ++ y_tail i).tail
        else (if i = coord.1 then [b] else []) ++ y_tail i) = y_tail := by
    funext i
    by_cases h : i = coord.1 <;> simp [h]
  ext i j
  simp only [listToBitString, Pi.add_apply, htail]
  by_cases h : i = coord.1 <;> simp [h]

private theorem listToBitString_eq_zero_of_not_mem {m k : ℕ}
    (coord : Fin m × Fin k) :
    ∀ (L : List (Fin m × Fin k)), coord ∉ L → ∀ (y_list : Fin m → List Bool),
      listToBitString L y_list coord.1 coord.2 = 0
  | [], _, _ => rfl
  | c :: L, hnot_mem, y_list => by
    rw [List.mem_cons, not_or] at hnot_mem
    obtain ⟨hne, hnot_L⟩ := hnot_mem
    have ih := listToBitString_eq_zero_of_not_mem coord L hnot_L
      (fun i => if i = c.1 then (y_list i).tail else y_list i)
    simp only [listToBitString, Pi.add_apply, ih, add_zero]
    by_cases h1 : coord.1 = c.1
    · have h2 : coord.2 ≠ c.2 := fun h2 => hne (Prod.ext h1 h2)
      simp [h1, Pi.single_eq_of_ne h2]
    · simp [h1]

private theorem extractOutBits_cons_add_single {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (hnot_mem : coord ∉ L)
    (b : Bool) (y_rest : Fin m → BitString k)
    (hy_coord : y_rest coord.1 coord.2 = 0) (i : Fin m) :
    extractOutBits (coord :: L)
      ((fun i' => if i' = coord.1 then Pi.single coord.2 b else 0) + y_rest) i =
    (if i = coord.1 then [b] else []) ++ extractOutBits L y_rest i := by
  dsimp only [extractOutBits, List.map_cons, List.flatten_cons, Pi.add_apply]
  refine congrArg₂ List.append ?_ ?_
  · by_cases hi : i = coord.1 <;> simp [hi, hy_coord]
  · refine congrArg List.flatten (List.map_congr_left fun c hc => ?_)
    have hne : c ≠ coord := fun h => hnot_mem (h ▸ hc)
    by_cases h1 : c.1 = coord.1
    · have h2 : c.2 ≠ coord.2 := fun h2 => hne (Prod.ext h1 h2)
      simp [h1, Pi.single_eq_of_ne h2]
    · simp [h1]

private theorem extractOutBits_listToBitString_cons {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (hnot_mem : coord ∉ L)
    (b : Bool) (y_tail : Fin m → List Bool) (i : Fin m) :
    extractOutBits (coord :: L)
      (listToBitString (coord :: L)
        (fun i' => (if i' = coord.1 then [b] else []) ++ y_tail i')) i =
    (if i = coord.1 then [b] else []) ++
      extractOutBits L (listToBitString L y_tail) i := by
  rw [listToBitString_cons,
    extractOutBits_cons_add_single coord L hnot_mem b (listToBitString L y_tail)
      (listToBitString_eq_zero_of_not_mem coord L hnot_mem y_tail)]

private theorem extractOutBits_outCoords {m k : ℕ}
    (y_out : Fin m → BitString k) (i : Fin m) :
    extractOutBits (GMWCircuit.outCoords m k) y_out i = List.ofFn (y_out i) := by
  have hJ : ∀ (r : Fin m) (J : List (Fin k)),
      extractOutBits (J.map fun j => (r, j)) y_out i =
        if i = r then J.map (y_out r) else [] := by
    intro r J
    induction J with
    | nil => simp [extractOutBits]
    | cons j J ih =>
      simp only [extractOutBits, List.map_cons, List.flatten_cons] at ih ⊢
      rw [ih]
      by_cases h : i = r <;> simp [h]
  have hR : ∀ R : List (Fin m),
      extractOutBits (R.flatMap fun r => (List.finRange k).map fun j => (r, j)) y_out i =
        (R.map fun r => if i = r then List.ofFn (y_out i) else []).flatten := by
    intro R
    induction R with
    | nil => rfl
    | cons r R ih =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ← ih]
      simp only [extractOutBits, List.map_append, List.flatten_append]
      congr 1
      change extractOutBits ((List.finRange k).map fun j => (r, j)) y_out i = _
      rw [hJ, ← List.ofFn_eq_map]
      by_cases h : i = r <;> simp [h]
  rw [GMWCircuit.outCoords, hR, flatten_map_ite_eq i (List.ofFn (y_out i)) (List.nodup_finRange m)]
  simp [List.mem_finRange]

private theorem nodup_outCoords (m k : ℕ) : (GMWCircuit.outCoords m k).Nodup := by
  rw [GMWCircuit.outCoords, List.nodup_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · exact (List.nodup_finRange k).map fun j₁ j₂ h => (Prod.mk.inj h).2
  · refine (List.nodup_finRange m).pairwise_of_forall_ne fun r₁ _ r₂ _ hne => ?_
    dsimp [Function.onFun]
    rw [List.disjoint_left]
    intro x hx₁ hx₂
    rw [List.mem_map] at hx₁ hx₂
    obtain ⟨j₁, _, rfl⟩ := hx₁
    obtain ⟨j₂, _, h₂⟩ := hx₂
    exact hne (Prod.mk.inj h₂).1.symm

private theorem dropPairsOTReceived_joinPairsOTReceived_double {m : ℕ} {α β : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k₁ : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → β →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (k₂ :
      (Schedule.compose (fun _ : (sharedMulSpec 2).Op => twoPartyMulSchedule) []).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i)
    (r_oracle : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties) ++ [])).Received i)
    (a : α) (b : β) :
    dropPairsOTReceived parties i L
      (joinPairsOTReceived parties i L k₁
        (joinPairsOTReceived parties i L k₂ r_oracle a) b) =
      k₁ (k₂ () a) b := by
  induction L with
  | nil =>
    cases r_oracle
    rfl
  | cons _ L ih =>
    rcases r_oracle with ⟨r_head, r_tail⟩
    exact ih r_tail

@[simp] private theorem encOutCoordsMsgReceived_join {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (i : Fin m)
    (r_oracle :
      (otMulCompose
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]).Received i)
    (r_gather : (otMulCompose (GMWCircuit.gatherSchedule m coord.1 (List.finRange m))).Received i)
    (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) :
    encOutCoordsMsgReceived i (coord :: L)
      (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L) i
        (joinOTMulCompose [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
          (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i r_oracle r_gather)
        r_rest) =
    encGatherOTReceived coord.1 i (List.finRange m) r_gather ++
      encOutCoordsMsgReceived i L r_rest := by
  dsimp only [encOutCoordsMsgReceived, GMWCircuit.coordSchedule, joinOTMulCompose]
  rw [dropPairsOTReceived_joinPairsOTReceived_double, splitOTMulCompose_joinOTMulCompose]

private theorem runSharedMulSteps_append_of_pure {m : ℕ} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m (sharedMulSpec m)}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (c₂ : ((i : Fin m) → Mid i) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) sc₂) i)
    (r₂ : ((i : Fin m) → Mid i) → (i : Fin m) → (otMulCompose sc₂).Received i)
    (out₂ : ((i : Fin m) → Mid i) → (i : Fin m) → Out i)
    (h₂ : ∀ st₁, runSharedMulSteps steps₂ st₁ = pure (c₂ st₁, r₂ st₁, out₂ st₁))
    (st₀ : (i : Fin m) → State i) :
    runSharedMulSteps (steps₁.append steps₂) st₀ =
      (fun res₁ =>
        (fun i => joinOTSubCoins sc₁ sc₂ i (res₁.1 i) (c₂ res₁.2.2 i),
         fun i => joinOTMulCompose sc₁ sc₂ i (res₁.2.1 i) (r₂ res₁.2.2 i),
         out₂ res₁.2.2)) <$>
        runSharedMulSteps steps₁ st₀ := by
  rw [runSharedMulSteps_append]
  simp only [h₂, bind_pure_comp, map_pure]

private theorem runSharedMulSteps_singleCoordSteps {m k : ℕ} [NeZero m]
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k))
    (a_table : Fin m → Fin m → BitString k) (y_acc : Fin m → BitString k) :
    ((fun res =>
      (res.2.2,
       fun i =>
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i (res.2.1 i),
       fun (i : Fin m)
         (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
        encOutCoordsMsgReceived i (coord :: L)
          (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L)
            i (res.2.1 i) r_rest))) <$>
      runSharedMulSteps (GMWCircuit.singleCoordSteps m k coord) (fun i => (a_table i, y_acc i))) =
    (fun tr =>
      let mul := realSharedMulPure m
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
      (fun i =>
        (a_table i,
         y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, mul.1 s) else 0),
       mul.2.1,
       mul.2.2,
       fun (i : Fin m)
         (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
        (if i = coord.1 then List.ofFn mul.1 else []) ++
          encOutCoordsMsgReceived i L r_rest)) <$>
      realPairsCalls m
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) (orderedPairs m) := by
  have happ := runSharedMulSteps_append_of_pure
    (Steps.oracle (spec := sharedMulSpec m)
      (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
      (op := ()) (parties := Function.Embedding.refl (Fin m))
      (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
      (.done fun i st => (st.1, st.2 i rfl, (0 : Bool))))
    (GMWCircuit.gatherStepsWith coord.1
      (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
        (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
      (List.finRange m))
    (fun _ i => unitOTGatherSubCoins coord.1 i (List.finRange m))
    (fun st₁ i => deliverOTGather coord.1 (fun s => (st₁ s).2.1) (List.finRange m) i)
    (fun st₁ i =>
      ((st₁ i).1.1,
       (st₁ i).1.2 +
         if i = coord.1 then
           Pi.single coord.2
             ((st₁ i).2.2 +
               GMWCircuit.sumGatherBits (spec := sharedMulSpec m) coord.1 (List.finRange m) i
                 (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1
                   (fun s => (st₁ s).2.1) (List.finRange m) i))
         else 0))
    (runSharedMulSteps_gatherStepsWith coord.1 _ (List.finRange m))
    (fun i => (a_table i, y_acc i))
  have hmul := runSharedMulSteps_oracle_done
    (fun s (st : (Fin m → BitString k) × BitString k) =>
      (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
    (fun _ st b => (st, b, (0 : Bool)))
    (fun i => (a_table i, y_acc i))
  have hcongr := congrArg (Functor.map (f := WordOracleComp Unit)
    (fun p : ((Fin m → ((Fin m → BitString k) × BitString k) × Bool × Bool) ×
        (Fin m → List Bool) × (Fin m → List Bool)) =>
      (fun i =>
        ((p.1 i).1.1,
         (p.1 i).1.2 +
           if i = coord.1 then
             Pi.single coord.2
               ((p.1 i).2.2 +
                 GMWCircuit.sumGatherBits (spec := sharedMulSpec m) coord.1 (List.finRange m) i
                   (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1
                     (fun s => (p.1 s).2.1) (List.finRange m) i))
           else 0),
       p.2.1,
       p.2.2,
       fun (i : Fin m)
         (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
        encGatherOTReceived coord.1 i (List.finRange m)
          (deliverOTGather coord.1 (fun s => (p.1 s).2.1) (List.finRange m) i) ++
          encOutCoordsMsgReceived i L r_rest))) hmul
  have hbridge :
      ((fun res =>
        (res.2.2,
         fun i =>
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              (GMWCircuit.coordSchedule m coord.1))
            i (res.1 i),
         fun i =>
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              (GMWCircuit.coordSchedule m coord.1))
            i (res.2.1 i),
         fun (i : Fin m)
           (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
          encOutCoordsMsgReceived i (coord :: L)
            (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1)
              (GMWCircuit.outCoordsSchedule m L)
              i (res.2.1 i) r_rest))) <$>
        runSharedMulSteps (GMWCircuit.singleCoordSteps m k coord) (fun i => (a_table i, y_acc i))) =
      (fun p : ((Fin m → ((Fin m → BitString k) × BitString k) × Bool × Bool) ×
          (Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun i =>
          ((p.1 i).1.1,
           (p.1 i).1.2 +
             if i = coord.1 then
               Pi.single coord.2
                 ((p.1 i).2.2 +
                   GMWCircuit.sumGatherBits (spec := sharedMulSpec m) coord.1 (List.finRange m) i
                     (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1
                       (fun s => (p.1 s).2.1) (List.finRange m) i))
             else 0),
         p.2.1,
         p.2.2,
         fun (i : Fin m)
           (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
          encGatherOTReceived coord.1 i (List.finRange m)
            (deliverOTGather coord.1 (fun s => (p.1 s).2.1) (List.finRange m) i) ++
            encOutCoordsMsgReceived i L r_rest)) <$>
        ((fun res =>
          (res.2.2,
           fun i =>
            encOTSubCoins
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
              i (res.1 i),
           fun i =>
            encOTOracleAnswers
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
              i (res.2.1 i))) <$>
          runSharedMulSteps (State := fun _ => (Fin m → BitString k) × BitString k)
            (.oracle (spec := sharedMulSpec m) (op := ())
              (parties := Function.Embedding.refl (Fin m))
              (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
              (.done fun i st => (st.1, st.2 i rfl, (0 : Bool))))
            (fun i => (a_table i, y_acc i))) := by
    rw [singleCoordSteps_eq_append, happ, Functor.map_map, Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun res₁ => ?_)
    dsimp only [Function.comp_def]
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_)
      (Prod.ext (funext fun i => ?_) (funext fun i => funext fun r_rest => ?_)))
    · exact (encOTSubCoins_joinOTSubCoins
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i (res₁.1 i)
        (unitOTGatherSubCoins coord.1 i (List.finRange m))).trans (by simp)
    · exact (encOTOracleAnswers_joinOTMulCompose
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i (res₁.2.1 i)
        (deliverOTGather coord.1 (fun s => (res₁.2.2 s).2.1) (List.finRange m) i)).trans (by simp)
    · exact encOutCoordsMsgReceived_join coord L i (res₁.2.1 i)
        (deliverOTGather coord.1 (fun s => (res₁.2.2 s).2.1) (List.finRange m) i) r_rest
  rw [hbridge, hcongr, Functor.map_map]
  refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
  simp only [GMWCircuit.sumGatherBits_deliverGather, zero_add,
    encGatherOTReceived_deliverOTGather_finRange]
  refine Prod.ext (funext fun i => Prod.ext rfl ?_) rfl
  by_cases h : i = coord.1 <;> simp [h]

private theorem runSharedMulSteps_outCoordsSteps_add {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k)
    (y : Fin m → BitString k) (L : List (Fin m × Fin k))
    (y_acc : Fin m → BitString k) :
    ((fun res =>
      (res.2.2,
       fun i =>
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i (res.2.1 i),
       fun i =>
        encOutCoordsMsgReceived i L (res.2.1 i))) <$>
      runSharedMulSteps (GMWCircuit.outCoordsSteps m k L) (fun i => (a_table i, y_acc i))) =
    (fun acc3 : Step3Acc m =>
      (y_acc + listToBitString L acc3.2.2.2,
       acc3.1, acc3.2.1, acc3.2.2.1)) <$>
      foldlMList (realOutStep m) (itemsOfCoords I a_table y L) (zeroStep3Acc m) := by
  induction L generalizing y_acc with
  | nil =>
    simp [GMWCircuit.outCoordsSteps, GMWCircuit.outCoordsSchedule, itemsOfCoords,
      zeroStep3Acc, listToBitString, encOutCoordsMsgReceived]
  | cons coord L ih =>
    rw [GMWCircuit.outCoordsSteps, runSharedMulSteps_append]
    simp only [GMWCircuit.outCoordsSchedule, map_bind, bind_pure_comp, Functor.map_map,
      encOTSubCoins_joinOTSubCoins, encOTOracleAnswers_joinOTMulCompose]
    have hstep1 := congrArg
      (· >>= fun p =>
        (fun q_tail =>
          (q_tail.1,
           fun i => p.2.1 i ++ q_tail.2.1 i,
           fun i => p.2.2.1 i ++ q_tail.2.2.1 i,
           fun i => p.2.2.2 i (q_tail.2.2.2 i))) <$>
        ((fun res₂ =>
          (res₂.2.2,
           fun i =>
            encOTSubCoins
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                (GMWCircuit.outCoordsSchedule m L))
              i (res₂.1 i),
           fun i =>
            encOTOracleAnswers
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                (GMWCircuit.outCoordsSchedule m L))
              i (res₂.2.1 i),
           fun i => res₂.2.1 i)) <$>
          runSharedMulSteps (GMWCircuit.outCoordsSteps m k L) p.1))
      (runSharedMulSteps_singleCoordSteps coord L a_table y_acc)
    simp only [bind_map_left, Functor.map_map] at hstep1
    rw [hstep1]
    simp only [itemsOfCoords, List.map_cons, foldlMList_cons, realOutStep,
      appendStep3Acc_zero_left, realOutCore, bind_map_left, map_bind]
    refine congrArg (Bind.bind _) (funext fun tr => ?_)
    let mul := realSharedMulPure m
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
    have hih := congrArg
      (Functor.map (f := WordOracleComp Unit)
        (fun q_tail :
            (Fin m → BitString k) × (Fin m → List Bool) ×
              (Fin m → List Bool) × (Fin m → List Bool) =>
          (q_tail.1,
           fun i => mul.2.1 i ++ q_tail.2.1 i,
           fun i => mul.2.2 i ++ q_tail.2.2.1 i,
           fun i => (if i = coord.1 then List.ofFn mul.1 else []) ++ q_tail.2.2.2 i)))
      (ih (fun i => y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, mul.1 s) else 0))
    simp only [Functor.map_map] at hih
    rw [hih, foldlMList_realOutStep_eq_map _ (finishOutStep m coord.1 mul), Functor.map_map]
    dsimp only [Function.comp_def, appendStep3Acc, finishOutStep]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun acc_tail => ?_)
    refine Prod.ext ?_ rfl
    rw [listToBitString_cons, ← add_assoc]
    rfl

private theorem map_extractOutBits_foldlMList_realOutStep {m k : ℕ} [NeZero m]
    {β : Type} (f : Step3Acc m → (Fin m → List Bool) → β)
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k) (y : Fin m → BitString k)
    {L : List (Fin m × Fin k)} (hL : L.Nodup) :
    ((fun acc3 => f acc3 (extractOutBits L (listToBitString L acc3.2.2.2))) <$>
      foldlMList (realOutStep m) (itemsOfCoords I a_table y L) (zeroStep3Acc m)) =
    ((fun acc3 => f acc3 acc3.2.2.2) <$>
      foldlMList (realOutStep m) (itemsOfCoords I a_table y L) (zeroStep3Acc m)) := by
  induction L generalizing f with
  | nil =>
    have hex : extractOutBits ([] : List (Fin m × Fin k)) (listToBitString [] fun _ => []) =
        fun _ => [] := rfl
    simp [itemsOfCoords, zeroStep3Acc, hex]
  | cons coord L ih =>
    rw [List.nodup_cons] at hL
    have hcons :
        itemsOfCoords I a_table y (coord :: L) =
          (coord.1, fun s => a_table s coord.1 coord.2,
            if coord.1 ∈ I then y coord.1 coord.2 else false) ::
            itemsOfCoords I a_table y L := rfl
    rw [hcons]
    simp only [foldlMList_cons, realOutStep, appendStep3Acc_zero_left,
      realOutCore, bind_map_left, map_bind]
    refine congrArg (Bind.bind _) (funext fun tr => ?_)
    let mul := realSharedMulPure m
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
    rw [foldlMList_realOutStep_eq_map _ (finishOutStep m coord.1 mul),
      Functor.map_map, Functor.map_map]
    have hstep (acc_tail : Step3Acc m) :
        extractOutBits (coord :: L)
          (listToBitString (coord :: L)
            (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail).2.2.2) =
        fun i =>
          (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++
            extractOutBits L (listToBitString L acc_tail.2.2.2) i := by
      funext i
      exact extractOutBits_listToBitString_cons coord L hL.1 (∑ s : Fin m, mul.1 s) acc_tail.2.2.2 i
    have hfun :
        (fun a =>
          f (appendStep3Acc m (finishOutStep m coord.1 mul) a)
            (extractOutBits (coord :: L)
              (listToBitString (coord :: L)
                (appendStep3Acc m (finishOutStep m coord.1 mul) a).2.2.2))) =
        fun acc_tail =>
          f (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail)
            (fun i =>
              (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++
                extractOutBits L (listToBitString L acc_tail.2.2.2) i) :=
      funext fun acc_tail => congrArg (f _) (hstep acc_tail)
    rw [hfun,
      ih (fun acc_tail y_list =>
        f (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail)
          (fun i => (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++ y_list i)) hL.2]
    rfl

private theorem buildOutItems_eq_itemsOfCoords_of_getD {m n k : ℕ} (I : Finset (Fin m))
    (D : Circuit Boolean.signature n (m * k))
    (w : Fin m → Wire n D.size → Bool)
    (y_bits : Fin m → List Bool) (y : Fin m → BitString k)
    (hy : ∀ r ∈ I, ∀ j : Fin k, (y_bits r).getD j.val false = y r j) :
    buildOutItems m k I D.code.2 (fun s => wireToList (w s)) y_bits =
      itemsOfCoords I
        (fun s r j => w s (D.outputs (finProdFinEquiv (r, j))))
        y (GMWCircuit.outCoords m k) := by
  rw [← buildOutItems_eq_itemsOfCoords I D w y]
  dsimp only [buildOutItems]
  refine List.flatMap_congr fun r _ => List.map_congr_left fun j hj => ?_
  have hj_lt : j < k := List.mem_range.1 hj
  by_cases hr : r ∈ I
  · have h1 := hy r hr ⟨j, hj_lt⟩
    have h2 : (List.ofFn (y r)).getD j false = y r ⟨j, hj_lt⟩ := by
      simp [List.getD_eq_getElem?_getD, hj_lt]
    simp only [hr, ↓reduceIte, h1, h2]
  · simp only [hr, ↓reduceIte]

private theorem runSharedMulSteps_outputSteps {m n k : ℕ} [NeZero m]
    (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (c₂ a₂ : Fin m → List Bool) :
    ((fun res =>
      (fun i => c₂ i ++
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
          i (res.1 i),
       fun i => a₂ i ++
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
          i (res.2.1 i),
       fun i => encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) (res.2.1 i),
       fun i => List.ofFn (res.2.2 i))) <$>
      runSharedMulSteps (GMWCircuit.outputSteps m n k D) w) =
    foldlMList (realOutStep m)
      (buildOutItems m k Finset.univ D.code.2 (fun s => wireToList (w s)) (fun _ => []))
      (c₂, a₂, fun _ => [], fun _ => []) := by
  let a_table : Fin m → Fin m → BitString k :=
    fun s r j => w s (D.outputs (finProdFinEquiv (r, j)))
  have hitems :
      buildOutItems m k Finset.univ D.code.2 (fun s => wireToList (w s)) (fun _ => []) =
        itemsOfCoords Finset.univ a_table 0 (GMWCircuit.outCoords m k) :=
    buildOutItems_eq_itemsOfCoords_of_getD Finset.univ D w (fun _ => []) 0 (fun _ _ _ => rfl)
  rw [hitems, GMWCircuit.outputSteps, runSharedMulSteps_mapState,
    foldlMList_realOutStep_eq_map _ (c₂, a₂, fun _ => [], fun _ => [])]
  have hadd := congrArg
    (Functor.map (f := WordOracleComp Unit)
      (fun q :
          (Fin m → BitString k) × (Fin m → List Bool) ×
            (Fin m → List Bool) × (Fin m → List Bool) =>
        (fun i => c₂ i ++ q.2.1 i,
         fun i => a₂ i ++ q.2.2.1 i,
         q.2.2.2,
         fun i => List.ofFn (q.1 i))))
    (runSharedMulSteps_outCoordsSteps_add Finset.univ a_table 0 (GMWCircuit.outCoords m k) 0)
  simp only [Functor.map_map, zero_add] at hadd
  refine hadd.trans ?_
  simp only [← extractOutBits_outCoords]
  exact map_extractOutBits_foldlMList_realOutStep
    (fun acc3 y_list =>
      (fun i => c₂ i ++ acc3.1 i, fun i => a₂ i ++ acc3.2.1 i, acc3.2.2.1, y_list))
    Finset.univ a_table 0 (nodup_outCoords m k)

private theorem simSharedMulSteps_append_of_pure {m : ℕ} [NeZero m]
    {State Mid Out : Fin m → Type} {sc₁ sc₂ : Schedule m (sharedMulSpec m)}
    (I : Finset (Fin m))
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (stI : (i : I) → State i.1)
    (r₁ : (i : I) → sc₁.Received i.1) (r₂ : (i : I) → sc₂.Received i.1)
    (c₂ : (i : I) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) sc₂) i.1)
    (rec₂ : (i : I) → (otMulCompose sc₂).Received i.1)
    (h₂ : simSharedMulSteps I steps₂ (fun i => steps₁.outputAt i.1 (stI i) (r₁ i)) r₂ =
      pure (fun i => (c₂ i, rec₂ i))) :
    simSharedMulSteps I (steps₁.append steps₂) stI
      (fun i => Schedule.Received.append (r₁ i) (r₂ i)) =
    (fun res₁ (i : I) =>
      (joinOTSubCoins sc₁ sc₂ i.1 (res₁ i).1 (c₂ i),
       joinOTMulCompose sc₁ sc₂ i.1 (res₁ i).2 (rec₂ i))) <$>
      simSharedMulSteps I steps₁ stI r₁ := by
  rw [simSharedMulSteps_append]
  simp only [h₂, bind_pure_comp, map_pure]

private theorem simSharedMulSteps_singleCoordSteps {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (coord : Fin m × Fin k) (L : List (Fin m × Fin k))
    (a_table : Fin m → Fin m → BitString k) (y_acc : Fin m → BitString k)
    (ans : Fin m → Bool) :
    ((fun res (i : I) =>
      (encOTSubCoins
        (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
        i.1 (res i).1,
       encOTOracleAnswers
        (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
        i.1 (res i).2,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        encOutCoordsMsgReceived i.1 (coord :: L)
          (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L)
            i.1 (res i).2 r_rest))) <$>
      simSharedMulSteps I (GMWCircuit.singleCoordSteps m k coord)
        (fun i => (a_table i.1, y_acc i.1))
        (fun i => GMWCircuit.deliverCoord coord.1 ans i.1)) =
    (fun r (i : I) =>
      ((simSharedMulPure m I
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r).1 i.1,
       (simSharedMulPure m I
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r).2 i.1,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        (if i.1 = coord.1 then List.ofFn ans else []) ++
          encOutCoordsMsgReceived i.1 L r_rest)) <$>
      ProbComp.uniform (OrderedPair m → Bool) := by
  have happ :=
    simSharedMulSteps_append_of_pure (Out := fun _ : Fin m => (Fin m → BitString k) × BitString k) I
      (Steps.oracle (spec := sharedMulSpec m)
        (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
        (op := ()) (parties := Function.Embedding.refl (Fin m))
        (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
        (.done fun i st => (st.1, st.2 i rfl, (0 : Bool))))
      (GMWCircuit.gatherStepsWith coord.1
        (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
          (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
        (List.finRange m))
      (fun i => (a_table i.1, y_acc i.1))
      (fun i =>
        (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
          (Function.Embedding.refl (Fin m)) ans i.1, ()))
      (fun i =>
        GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1 ans (List.finRange m) i.1)
      (fun i => unitOTGatherSubCoins coord.1 i.1 (List.finRange m))
      (fun i => deliverOTGather coord.1 ans (List.finRange m) i.1)
      (simSharedMulSteps_gatherStepsWith I coord.1
        (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
          (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
        (List.finRange m) _ ans)
  have hmul := simSharedMulSteps_oracle_done I
    (fun s (st : (Fin m → BitString k) × BitString k) =>
      (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
    (fun i st => (st.1, st.2 i rfl, (0 : Bool)))
    (fun i => (a_table i.1, y_acc i.1))
    (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s))
    (fun _ => rfl) ans
  have hcongr := congrArg (Functor.map (f := ProbComp)
    (fun (p : (i : I) → List Bool × List Bool) (i : I) =>
      ((p i).1,
       (p i).2,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        (if i.1 = coord.1 then List.ofFn ans else []) ++
          encOutCoordsMsgReceived i.1 L r_rest))) hmul
  have hdeliv :
      (fun i : I => GMWCircuit.deliverCoord coord.1 ans i.1) =
      (fun i : I =>
        Schedule.Received.append
          (sc₁ := [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          (sc₂ := GMWCircuit.gatherSchedule m coord.1 (List.finRange m))
          (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
            (Function.Embedding.refl (Fin m)) ans i.1, ())
          (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1 ans (List.finRange m) i.1)) :=
    rfl
  have hbridge :
      ((fun res (i : I) =>
        (encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i.1 (res i).1,
         encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i.1 (res i).2,
         fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
          encOutCoordsMsgReceived i.1 (coord :: L)
            (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1)
              (GMWCircuit.outCoordsSchedule m L)
              i.1 (res i).2 r_rest))) <$>
        simSharedMulSteps I (GMWCircuit.singleCoordSteps m k coord)
          (fun i => (a_table i.1, y_acc i.1))
          (fun i => GMWCircuit.deliverCoord coord.1 ans i.1)) =
      (fun (p : (i : I) → List Bool × List Bool) (i : I) =>
        ((p i).1,
         (p i).2,
         fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
          (if i.1 = coord.1 then List.ofFn ans else []) ++
            encOutCoordsMsgReceived i.1 L r_rest)) <$>
        ((fun res (i : I) =>
          (encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
            i.1 (res i).1,
           encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
            i.1 (res i).2)) <$>
          simSharedMulSteps (State := fun _ => (Fin m → BitString k) × BitString k) I
            (.oracle (spec := sharedMulSpec m) (op := ())
              (parties := Function.Embedding.refl (Fin m))
              (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
              (.done fun i st => (st.1, st.2 i rfl, (0 : Bool))))
            (fun i => (a_table i.1, y_acc i.1))
            (fun i =>
              (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
                (Function.Embedding.refl (Fin m)) ans i.1, ()))) := by
    rw [singleCoordSteps_eq_append, hdeliv, happ, Functor.map_map, Functor.map_map]
    refine congrArg (Functor.map (f := ProbComp) · _) (funext fun res₁ => funext fun i => ?_)
    dsimp only [Function.comp_def]
    refine Prod.ext ?_ (Prod.ext ?_ (funext fun r_rest => ?_))
    · exact (encOTSubCoins_joinOTSubCoins
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i.1 (res₁ i).1
        (unitOTGatherSubCoins coord.1 i.1 (List.finRange m))).trans (by simp)
    · exact (encOTOracleAnswers_joinOTMulCompose
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i.1 (res₁ i).2
        (deliverOTGather coord.1 ans (List.finRange m) i.1)).trans (by simp)
    · exact (encOutCoordsMsgReceived_join coord L i.1 (res₁ i).2
        (deliverOTGather coord.1 ans (List.finRange m) i.1) r_rest).trans
        (by rw [encGatherOTReceived_deliverOTGather_finRange])
  rw [hbridge, hcongr, Functor.map_map]

private theorem eval_simSharedMulSteps_outCoordsSteps {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k)
    (y_acc : Fin m → BitString k) (yI : (i : I) → BitString k)
    (L : List (Fin m × Fin k)) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outCoordsDist m k (GMWCircuit.extendByZero I yI) L
      let res ← simSharedMulSteps I (GMWCircuit.outCoordsSteps m k L)
        (fun i => (a_table i.1, y_acc i.1)) (fun i => r_out i.1)
      return fun i : I =>
        (encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i.1 (res i).1,
         encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i.1 (res i).2,
         encOutCoordsMsgReceived i.1 L (res i).2)) =
    ProbComp.eval
      ((fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        foldlMList (simOutStep m I)
          (itemsOfCoords I a_table (GMWCircuit.extendByZero I yI) L) (zeroStep3Acc m)) := by
  induction L generalizing y_acc with
  | nil =>
    simp [GMWCircuit.outCoordsDist, GMWCircuit.outCoordsSteps, GMWCircuit.outCoordsSchedule,
      itemsOfCoords, zeroStep3Acc, encOutCoordsMsgReceived]
  | cons coord L ih =>
    have hy_coord :
        (if coord.1 ∈ I then GMWCircuit.extendByZero I yI coord.1 coord.2 else false) =
          GMWCircuit.extendByZero I yI coord.1 coord.2 := by
      by_cases h : coord.1 ∈ I <;> simp only [GMWCircuit.extendByZero, h, ↓reduceIte, ↓reduceDIte]
      rfl
    rw [GMWCircuit.outCoordsDist, GMWCircuit.outCoordsSteps]
    simp only [bind_assoc, bind_map_left, simSharedMulSteps_append, GMWCircuit.outCoordsSchedule,
      GMWCircuit.outputAt_singleCoordSteps, map_bind, bind_pure_comp, Functor.map_map,
      encOTSubCoins_joinOTSubCoins, encOTOracleAnswers_joinOTMulCompose,
      itemsOfCoords, List.map_cons, foldlMList_cons, simOutStep,
      appendStep3Acc_zero_left, simOutCore, hy_coord]
    rw [ProbComp.eval_bind, ProbComp.eval_bind]
    refine congrArg (PMF.bind _) (funext fun ans => ?_)
    have hstep1 (r_tail : (i : Fin m) → (GMWCircuit.outCoordsSchedule m L).Received i) :=
      congrArg
        (· >>= fun p =>
          Functor.map (f := ProbComp)
            (fun (q_tail : (i : I) →
                  List Bool × List Bool ×
                    (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1)
                (i : I) =>
              ((p i).1 ++ (q_tail i).1,
               (p i).2.1 ++ (q_tail i).2.1,
               (p i).2.2 (q_tail i).2.2))
          (Functor.map (f := ProbComp)
            (fun res₂ (i : I) =>
              (encOTSubCoins
                (Schedule.compose (fun _ => multiPartyMulSchedule m)
                  (GMWCircuit.outCoordsSchedule m L))
                i.1 (res₂ i).1,
               encOTOracleAnswers
                (Schedule.compose (fun _ => multiPartyMulSchedule m)
                  (GMWCircuit.outCoordsSchedule m L))
                i.1 (res₂ i).2,
               (res₂ i).2))
            (simSharedMulSteps I (GMWCircuit.outCoordsSteps m k L)
              (fun i =>
                (a_table i.1,
                 y_acc i.1 + if i.1 = coord.1 then Pi.single coord.2 (∑ s : Fin m, ans s) else 0))
              (fun i => r_tail i.1))))
        (simSharedMulSteps_singleCoordSteps I coord L a_table y_acc ans)
    simp only [bind_map_left, Functor.map_map] at hstep1
    simp_rw [hstep1, ProbComp.eval_bind]
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind _) (funext fun r => ?_)
    let mul := simSharedMulPure m I
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r
    have hih := congrArg
      (PMF.map fun q_tail (i : I) =>
        (mul.1 i.1 ++ (q_tail i).1,
         mul.2 i.1 ++ (q_tail i).2.1,
         (if i.1 = coord.1 then List.ofFn ans else []) ++ (q_tail i).2.2))
      (ih (fun i => y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, ans s) else 0))
    simp only [bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.map_bind, PMF.map_comp, Function.comp_def] at hih ⊢
    rw [hih, foldlMList_simOutStep_eq_map I _ (finishOutStep m coord.1 (ans, mul))]
    simp only [ProbComp.eval_map, PMF.map_comp, Function.comp_def,
      appendStep3Acc, finishOutStep, itemsOfCoords]

private theorem eval_simSharedMulSteps_outputSteps {m n k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (yI : (i : I) → BitString k)
    (c₂ a₂ : Fin m → List Bool) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outputDist m k (GMWCircuit.extendByZero I yI)
      let res ← simSharedMulSteps I (GMWCircuit.outputSteps m n k D)
        (I.restrict w) (I.restrict r_out)
      return fun i : I =>
        (c₂ i.1 ++
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).1,
         a₂ i.1 ++
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).2,
         encOutCoordsMsgReceived i.1 (GMWCircuit.outCoords m k) (res i).2)) =
    ProbComp.eval
      ((fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        foldlMList (simOutStep m I)
          (buildOutItems m k I D.code.2 (fun s => wireToList (w s))
            (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩) else List.replicate k false))
          (c₂, a₂, fun _ => [], fun _ => [])) := by
  let a_table : Fin m → Fin m → BitString k :=
    fun s r j => w s (D.outputs (finProdFinEquiv (r, j)))
  have hitems :
      buildOutItems m k I D.code.2 (fun s => wireToList (w s))
        (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩) else List.replicate k false) =
      itemsOfCoords I a_table (GMWCircuit.extendByZero I yI) (GMWCircuit.outCoords m k) := by
    refine buildOutItems_eq_itemsOfCoords_of_getD I D w _ _ fun r hr j => ?_
    simp [hr, GMWCircuit.extendByZero, List.getD_eq_getElem?_getD]
  rw [hitems, GMWCircuit.outputDist, GMWCircuit.outputSteps,
    foldlMList_simOutStep_eq_map I _ (c₂, a₂, fun _ => [], fun _ => [])]
  simp_rw [simSharedMulSteps_mapState]
  have hout := congrArg
    (PMF.map fun q (i : I) => (c₂ i.1 ++ (q i).1, a₂ i.1 ++ (q i).2.1, (q i).2.2))
    (eval_simSharedMulSteps_outCoordsSteps I a_table 0 yI (GMWCircuit.outCoords m k))
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.map_bind, PMF.map_comp, PMF.pure_map,
    Function.comp_def, I.restrict_def, appendStep3Acc, List.nil_append] at hout ⊢
  exact hout

/-! #### Sub-part 4C.5: End-to-End Runner & Simulator Equivalence -/

private theorem eval_sampleList_eq_map_uniform (n : ℕ) :
    ProbComp.eval (Cslib.BitString.sampleList n) =
      ProbComp.eval (List.ofFn <$> ProbComp.uniform (BitString n)) := by
  rw [Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    ProbComp.eval_map, ProbComp.eval_uniform]

private theorem eval_sampleList_eq_map_uniform_blocks (N d : ℕ) :
    ProbComp.eval (Cslib.BitString.sampleList (N * d)) =
      ProbComp.eval
        ((fun c : Fin N → Fin d → Bool =>
            List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := d)).symm c)) <$>
          ProbComp.uniform (Fin N → Fin d → Bool)) := by
  rw [Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    ProbComp.eval_map, ProbComp.eval_uniform,
    ← PMF.uniformOfFintype_map_equiv
      (Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := d)).symm,
    PMF.map_comp]
  rfl

private theorem eval_sampleTwoPiBits_real (m coins N : ℕ) :
    ProbComp.eval (sampleTwoPiBits m (fun _ => coins) (fun _ => N * (m - 1))) =
      ProbComp.eval (do
        let r ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins))
        let c₁ ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool))
        return (fun i => List.ofFn (r i),
          fun i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i)))) := by
  have hr :
      ProbComp.eval (OracleComp.pi (fun _ : Fin m => Cslib.BitString.sampleList coins)) =
        (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).map
          (fun r i => List.ofFn (r i)) := by
    rw [ProbComp.eval_pi_congr (fun _ => eval_sampleList_eq_map_uniform coins),
      ProbComp.eval_pi_map]
  have hc :
      ProbComp.eval (OracleComp.pi (fun _ : Fin m => Cslib.BitString.sampleList (N * (m - 1)))) =
        (ProbComp.eval
          (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool)))).map
          (fun c₁ i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i))) := by
    rw [ProbComp.eval_pi_congr (fun _ => eval_sampleList_eq_map_uniform_blocks N (m - 1)),
      ProbComp.eval_pi_map]
  simp [sampleTwoPiBits, ProbComp.eval_bind, ProbComp.eval_map, hr, hc,
    PMF.bind_map, PMF.map_comp, Function.comp_def]

private theorem eval_sampleTwoPiBits_sim (m coins N : ℕ) (I : Finset (Fin m)) :
    ProbComp.eval
      (sampleTwoPiBits m (fun i => if i ∈ I then coins else 0) (fun _ => N * (m - 1))) =
    ProbComp.eval (do
      let rI ← OracleComp.piRestrict (α := fun _ => BitString coins) I
        (fun _ : I => ProbComp.uniform (BitString coins))
      let c₁ ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool))
      return (fun i => if hi : i ∈ I then List.ofFn (rI ⟨i, hi⟩) else [],
        fun i =>
          List.ofFn
            ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i)))) := by
  have hr_coord (i : Fin m) :
      ProbComp.eval (Cslib.BitString.sampleList (if i ∈ I then coins else 0)) =
        ProbComp.eval
          ((fun r_i : BitString coins => if i ∈ I then List.ofFn r_i else []) <$>
            ProbComp.uniform (BitString coins)) := by
    by_cases hi : i ∈ I
    · simp only [hi, ↓reduceIte, eval_sampleList_eq_map_uniform, ProbComp.eval_map]
    · simp [hi, Cslib.BitString.sampleList, ProbComp.eval_map, PMF.map, Function.comp_def]
  have hr :
      ProbComp.eval
        (OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (if i ∈ I then coins else 0))) =
      (ProbComp.eval
        (OracleComp.piRestrict (α := fun _ => BitString coins) I
          (fun _ : I => ProbComp.uniform (BitString coins)))).map
        (fun rI i => if hi : i ∈ I then List.ofFn (rI ⟨i, hi⟩) else []) := by
    have hrest :
        (fun _ : I => ProbComp.uniform (BitString coins)) =
          I.restrict (fun _ : Fin m => ProbComp.uniform (BitString coins)) := rfl
    rw [ProbComp.eval_pi_congr hr_coord, ProbComp.eval_pi_map, hrest,
      ← ProbComp.eval_map_restrict_pi I (fun _ : Fin m => ProbComp.uniform (BitString coins)),
      PMF.map_comp]
    refine congrArg (PMF.map · _) (funext fun r => funext fun i => ?_)
    by_cases hi : i ∈ I <;> simp [hi, I.restrict_def]
  have hc :
      ProbComp.eval (OracleComp.pi (fun _ : Fin m => Cslib.BitString.sampleList (N * (m - 1)))) =
        (ProbComp.eval
          (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool)))).map
          (fun c₁ i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i))) := by
    rw [ProbComp.eval_pi_congr (fun _ => eval_sampleList_eq_map_uniform_blocks N (m - 1)),
      ProbComp.eval_pi_map]
  simp [sampleTwoPiBits, ProbComp.eval_bind, ProbComp.eval_map, hr, hc,
    PMF.bind_map, PMF.map_comp, Function.comp_def]

private theorem step1SenderShare_congr_getD {m N : ℕ} (u v c1_s : List Bool) (i : Fin m)
    (h : ∀ j < N, u.getD j false = v.getD j false) :
    step1SenderShare m N u c1_s i = step1SenderShare m N v c1_s i := by
  refine List.map_congr_left fun j hj => ?_
  rw [h j (List.mem_range.mp hj)]

private theorem step1Wires_sim_ofFn {m n coins : ℕ} (I : Finset (Fin m))
    (xI : (i : I) → BitString n) (rI : (i : I) → BitString coins)
    (c : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) (i : Fin m) :
    step1Wires m (n + coins)
      (fun s => if hs : s ∈ I then List.ofFn (xI ⟨s, hs⟩) else List.replicate n false)
      (fun s => if hs : s ∈ I then List.ofFn (rI ⟨s, hs⟩) else [])
      (fun s =>
        List.ofFn
          ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c s)))
      i =
    List.ofFn (Cslib.BitString.blocksEquiv.symm
      (fun s =>
        GMWCircuit.shareInputBits m (n + coins)
          (GMWCircuit.extendByZero I (fun j => Fin.append (xI j) (rI j)) s) (c s) i)) := by
  dsimp only [step1Wires]
  rw [Cslib.BitString.ofFn_blocksEquiv_symm, List.ofFn_eq_map, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun s _ => ?_)
  rw [← step1SenderShare_ofFn]
  refine step1SenderShare_congr_getD _ _ _ i fun j hj => ?_
  by_cases hs : s ∈ I
  · simp only [hs, ↓reduceDIte, GMWCircuit.extendByZero, ofFn_fin_append]
  · simp only [hs, ↓reduceDIte, List.append_nil, GMWCircuit.extendByZero]
    have h1 : (List.replicate n false).getD j false = false := by
      by_cases hjn : j < n <;> simp [List.getD_eq_getElem?_getD, hjn]
    have h2 : (List.ofFn (0 : BitString (n + coins))).getD j false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj),
        Option.getD_some, List.getElem_ofFn]
      rfl
    exact h1.trans h2.symm

private theorem encGMWPartyView_of_join {m coins n k : ℕ}
    (C : Circuit Boolean.signature (m * n + coins) (m * k)) (i : Fin m)
    (x_i : BitString n) (r_i : BitString coins)
    (c1_i : Fin (n + coins) → Fin (m - 1) → Bool)
    (c_mul_i :
      Schedule.SubCoins (spec₁ := sharedMulSpec m) (fun _ _ => Unit)
        (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))) i)
    (inbox_i : Fin m → BitString (n + coins))
    (c_prog :
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i)
    (c_out :
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.outputSchedule m k)) i)
    (r_prog :
      (otMulCompose
        (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)).Received i)
    (r_out : (otMulCompose (GMWCircuit.outputSchedule m k)).Received i) :
    encGMWPartyView m coins n k C i
      ⟨x_i,
       (r_i,
        ((c1_i, c_mul_i),
         joinOTSubCoins (GMWCircuit.inputShareSchedule m (n + coins))
           (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program ++
             GMWCircuit.outputSchedule m k) i
           (unitOTMsgSubCoins i (GMWCircuit.allPairs m))
           (joinOTSubCoins
             (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)
             (GMWCircuit.outputSchedule m k) i c_prog c_out))),
       joinOTMulCompose (GMWCircuit.inputShareSchedule m (n + coins))
         (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program ++
           GMWCircuit.outputSchedule m k) i
         (receivedOTMsgScheduleOfInbox i inbox_i (GMWCircuit.allPairs m))
         (joinOTMulCompose
           (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)
           (GMWCircuit.outputSchedule m k) i r_prog r_out)⟩ =
    encPair
      (encPair (encPair encBits encBits) (encPair encBits encBits))
      (encPair encBits (encPair encBits encBits))
      (((List.ofFn x_i, List.ofFn r_i),
        (List.ofFn
           ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm c1_i),
         encOTSubCoins
           (Schedule.compose (fun _ => multiPartyMulSchedule m)
             (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i c_prog ++
           encOTSubCoins
             (Schedule.compose (fun _ => multiPartyMulSchedule m)
               (GMWCircuit.outputSchedule m k)) i c_out)),
       (List.ofFn (Cslib.BitString.blocksEquiv.symm inbox_i),
        (encOTOracleAnswers
           (Schedule.compose (fun _ => multiPartyMulSchedule m)
             (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i r_prog ++
           encOTOracleAnswers
             (Schedule.compose (fun _ => multiPartyMulSchedule m)
               (GMWCircuit.outputSchedule m k)) i r_out,
         encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) r_out))) := by
  simp only [encGMWPartyView, gmwCircuitSchedule, splitOTMulCompose_joinOTMulCompose,
    encOTSubCoins_joinOTSubCoins, encOTSubCoins_msgSchedule,
    encOTOracleAnswers_joinOTMulCompose, encOTOracleAnswers_msgSchedule,
    encPairsMsgReceived_allPairs, List.nil_append]

private theorem runSharedMulSteps_gmwCircuitSteps {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k))
    (x : Fin m → BitString n) (r : Fin m → BitString coins)
    (c₁ : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) :
    let D := C.comp (xorPreludeCircuit m n coins)
    let x_bits : Fin m → List Bool := fun s => List.ofFn (x s)
    let r_bits : Fin m → List Bool := fun s => List.ofFn (r s)
    let c1_bits : Fin m → List Bool := fun s =>
      List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c₁ s))
    let in_shares := step1Wires m (n + coins) x_bits r_bits c1_bits
    ((fun res =>
      encodeViewsAndOutputs (encGMWPartyView m coins n k C) (fun _ y => List.ofFn y)
        (fun i =>
          ⟨x i,
           (r i, ((c₁ i, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i), res.1 i)),
           res.2.1 i⟩,
         res.2.2)) <$>
      runSharedMulSteps (gmwCircuitProtocol m (n + coins) k D).steps
        (fun i => (Fin.append (x i) (r i), c₁ i))) =
    (do
      let acc2 ← foldlMList (realGateStep m) D.code.1 (in_shares, fun _ => [], fun _ => [])
      let outItems := buildOutItems m k Finset.univ D.code.2 acc2.1 (fun _ => [])
      let acc3 ← foldlMList (realOutStep m) outItems (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
      return packRealOutput m x_bits r_bits c1_bits in_shares acc3) := by
  intro D x_bits r_bits c1_bits in_shares
  let st : Fin m → BitString (m * (n + coins)) :=
    fun i => Cslib.BitString.blocksEquiv.symm
      (fun s => GMWCircuit.shareInputBits m (n + coins) (Fin.append (x s) (r s)) (c₁ s) i)
  have hst : (fun i => List.ofFn (st i)) = in_shares :=
    funext fun i => (step1Wires_ofFn x r c₁ i).symm
  dsimp only [gmwCircuitProtocol]
  rw [runSharedMulSteps_append, runSharedMulSteps_inputShareSteps, pure_bind,
    runSharedMulSteps_append]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  have hstep3 (res₂ :
      ((i : Fin m) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.progSchedule m D.program)) i) ×
      ((i : Fin m) → (otMulCompose (GMWCircuit.progSchedule m D.program)).Received i) ×
      ((i : Fin m) → Wire (m * (n + coins)) D.size → Bool)) :
      ((fun res₃ =>
        encodeViewsAndOutputs (encGMWPartyView m coins n k C) (fun _ y => List.ofFn y)
          (fun i =>
            ⟨x i,
             (r i,
              ((c₁ i, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i),
               joinOTSubCoins (GMWCircuit.inputShareSchedule m (n + coins))
                 (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i
                 (unitOTMsgSubCoins i (GMWCircuit.allPairs m))
                 (joinOTSubCoins (GMWCircuit.progSchedule m D.program)
                   (GMWCircuit.outputSchedule m k) i (res₂.1 i) (res₃.1 i)))),
             joinOTMulCompose (GMWCircuit.inputShareSchedule m (n + coins))
               (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i
               (receivedOTMsgScheduleOfInbox i
                 (fun s =>
                   GMWCircuit.shareInputBits m (n + coins) (Fin.append (x s) (r s)) (c₁ s) i)
                 (GMWCircuit.allPairs m))
               (joinOTMulCompose (GMWCircuit.progSchedule m D.program)
                 (GMWCircuit.outputSchedule m k) i (res₂.2.1 i) (res₃.2.1 i))⟩,
           res₃.2.2)) <$>
        runSharedMulSteps (GMWCircuit.outputSteps m (n + coins) k D) res₂.2.2) =
      (packRealOutput m x_bits r_bits c1_bits in_shares <$>
        foldlMList (realOutStep m)
          (buildOutItems m k Finset.univ D.code.2 (packStep2 res₂).1 (fun _ => []))
          ((packStep2 res₂).2.1, (packStep2 res₂).2.2, fun _ => [], fun _ => [])) := by
    dsimp only [packStep2]
    rw [← runSharedMulSteps_outputSteps D res₂.2.2
      (fun i => encOTSubCoins _ i (res₂.1 i))
      (fun i => encOTOracleAnswers _ i (res₂.2.1 i)),
      Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun res₃ => ?_)
    dsimp only [Function.comp_def, encodeViewsAndOutputs, packRealOutput, packPartyViewWord]
    congr 1
    refine Prod.ext (List.map_congr_left fun i _ => ?_) rfl
    rw [encGMWPartyView_of_join, ← hst]
    rfl
  simp_rw [hstep3]
  have hprog := congrArg
    (· >>= fun acc2 =>
      packRealOutput m x_bits r_bits c1_bits in_shares <$>
        foldlMList (realOutStep m)
          (buildOutItems m k Finset.univ D.code.2 acc2.1 (fun _ => []))
          (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []))
    (runSharedMulSteps_progSteps D.program st)
  simp only [bind_map_left, hst] at hprog
  exact hprog

private theorem eval_pi_gmwSampleCoins {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k)) :
    ProbComp.eval (OracleComp.pi (gmwOT14RandomizedProtocol m coins n k C).sampleCoins) =
      ProbComp.eval (do
        let rc ← (do
          let r ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins))
          let c₁ ← OracleComp.pi
            (fun _ : Fin m => ProbComp.uniform (Fin (n + coins) → Fin (m - 1) → Bool))
          pure (r, c₁))
        let c_ot ← OracleComp.pi
          (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins)))))
        pure fun i =>
          (rc.1 i,
           ((rc.2 i,
             unitSubCoins
               (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))) i),
            c_ot i))) := by
  dsimp only [gmwOT14RandomizedProtocol, Protocol.randomizedWrapper, Protocol.mapInput,
    gmwOT14Protocol, Protocol.compose, gmwCircuitProtocol]
  simp only [eval_pi_pair, eval_pi_sampleSubCoins_multiPartyMul,
    ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.pure_map, PMF.pure_bind, PMF.bind_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  rfl

private theorem runWith_realRunWord_eq_runEncoded {α : Type} (m : ℕ) [NeZero m]
    (coins n k : α → ℕ)
    (C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a))
    (inp : FamilyRunInput α m n)
    {OState : Type} (oracle : Unit × List Bool → StateT OState PMF (List Bool)) (s : OState) :
    ProbOracleComp.runWith oracle
      (realRunWord m coins n k
        (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code) inp) s =
    ProbOracleComp.runWith oracle
      ((gmwOT14RandomizedProtocol m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)).runEncoded
        (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1))
        (fun _ y => List.ofFn y) inp.2) s := by
  rcases inp with ⟨a, x⟩
  let D := (C a).comp (xorPreludeCircuit m (n a) (coins a))
  dsimp only [Protocol.runEncoded]
  rw [runWith_sample_congr_eq oracle _ _ (eval_pi_gmwSampleCoins (C a))]
  have hsteps (rc : (Fin m → BitString (coins a)) ×
      (Fin m → Fin (n a + coins a) → Fin (m - 1) → Bool)) (s₁ : OState) :
      ProbOracleComp.runWith oracle (do
        let c_ot ← ProbOracleComp.sample
          (OracleComp.pi
            (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                (gmwCircuitSchedule m (n a + coins a) (k a) D))))
        let recv ←
          (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)).steps.runEncoded
            (fun i =>
              (x i,
               (rc.1 i,
                ((rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i), c_ot i))))
        let views : (i : Fin m) → _ := fun i =>
          ⟨x i,
           (rc.1 i,
            ((rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i), c_ot i)),
           recv i⟩
        return encodeViewsAndOutputs (encGMWPartyView m (coins a) (n a) (k a) (C a))
          (fun _ y => List.ofFn y)
          (views,
           fun i =>
             (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)).outputOfView i
               (views i))) s₁ =
      ProbOracleComp.runWith oracle (do
        let x_bits : Fin m → List Bool := fun i => List.ofFn (x i)
        let r_bits : Fin m → List Bool := fun i => List.ofFn (rc.1 i)
        let c1_bits : Fin m → List Bool := fun i =>
          List.ofFn
            ((Cslib.BitString.blocksEquiv
              (α := Bool) (m := n a + coins a) (k := m - 1)).symm (rc.2 i))
        let in_shares := step1Wires m (n a + coins a) x_bits r_bits c1_bits
        let acc2 ← foldlMList (realGateStep m) D.code.1 (in_shares, fun _ => [], fun _ => [])
        let outItems := buildOutItems m (k a) Finset.univ D.code.2 acc2.1 (fun _ => [])
        let acc3 ←
          foldlMList (realOutStep m) outItems (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
        return packRealOutput m x_bits r_bits c1_bits in_shares acc3) s₁ := by
    let steps₂ :=
      ((gmwCircuitProtocol m (n a + coins a) (k a) D).compose
        (fun _ => multiPartyMulProtocol m)).steps
    let st₂ : (i : Fin m) → _ := fun i =>
      (Fin.append (x i) (rc.1 i),
       (rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i))
    have hlhs :
        (do
          let c_ot ← ProbOracleComp.sample
            (OracleComp.pi
              (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
                (Schedule.compose (fun _ => multiPartyMulSchedule m)
                  (gmwCircuitSchedule m (n a + coins a) (k a) D))))
          let recv ←
            (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)).steps.runEncoded
              (fun i =>
                (x i,
                 (rc.1 i,
                  ((rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i),
                   c_ot i))))
          let views : (i : Fin m) → _ := fun i =>
            ⟨x i,
             (rc.1 i,
              ((rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i), c_ot i)),
             recv i⟩
          return encodeViewsAndOutputs (encGMWPartyView m (coins a) (n a) (k a) (C a))
            (fun _ y => List.ofFn y)
            (views,
             fun i =>
               (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)).outputOfView i
                 (views i))) =
        ((fun res =>
          encodeViewsAndOutputs (encGMWPartyView m (coins a) (n a) (k a) (C a))
            (fun _ y => List.ofFn y)
            (fun i =>
              ⟨x i,
               (rc.1 i,
                ((rc.2 i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i), res.1 i)),
               res.2.1 i⟩,
             res.2.2)) <$>
          (do
            let c_ot ← ProbOracleComp.sample
              (OracleComp.pi
                (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
                  (Schedule.compose (fun _ => multiPartyMulSchedule m)
                    (gmwCircuitSchedule m (n a + coins a) (k a) D))))
            let recv ←
              (Composition.Steps.compose (fun _ => twoPartyMulProtocol) steps₂).runEncoded
                (fun i => (st₂ i, c_ot i))
            return (c_ot, recv,
              fun i =>
                (Composition.Steps.compose (fun _ => twoPartyMulProtocol) steps₂).outputAt i
                  (st₂ i, c_ot i) (recv i)))) := by
      simp [D, steps₂, st₂, gmwOT14RandomizedProtocol, Protocol.randomizedWrapper,
        Protocol.mapInput, gmwOT14Protocol, Protocol.compose, Protocol.outputOfView,
        Steps.runEncoded_mapState, Steps.outputAt_mapState, map_bind, bind_pure_comp,
        Functor.map_map]
    have hrunOT :
        runOTSteps steps₂ st₂ =
          runSharedMulSteps (gmwCircuitProtocol m (n a + coins a) (k a) D).steps
            (fun i => (Fin.append (x i) (rc.1 i), rc.2 i)) := by
      simp [steps₂, st₂, Protocol.compose, runSharedMulSteps, runOTSteps_mapState]
    rw [hlhs, ProbOracleComp.runWith_map,
      runWith_sample_runEncoded_compose_twoPartyMul oracle steps₂ st₂ s₁,
      hrunOT, ← ProbOracleComp.runWith_map]
    exact congrArg (fun p => ProbOracleComp.runWith oracle p s₁)
      (runSharedMulSteps_gmwCircuitSteps (C a) x rc.1 rc.2)
  rw [realRunWord]
  rw [runWith_sample_congr_eq oracle _ _ (eval_sampleTwoPiBits_real m (coins a) (n a + coins a))]
  simp only [ProbOracleComp.sample_bind, ProbOracleComp.sample_pure,
    bind_assoc, pure_bind, ProbOracleComp.runWith_bind]
  refine congrArg (PMF.bind _) (funext fun ⟨r, s₁⟩ => ?_)
  refine congrArg (PMF.bind _) (funext fun ⟨c₁, s₂⟩ => ?_)
  simpa only [ProbOracleComp.runWith_bind] using (hsteps (r, c₁) s₂).symm

private noncomputable def simOutStepProj (m k : ℕ) [NeZero m] (I : Finset (Fin m))
    (outs : List ℕ) (y_bits : Fin m → List Bool)
    (accI : (Fin m → List Bool) × ((i : I) → List Bool) × ((i : I) → List Bool)) :
    ProbComp ((i : I) → List Bool × List Bool × List Bool) :=
  (fun acc (i : I) => (accI.2.1 i ++ acc.1 i.1, accI.2.2 i ++ acc.2.1 i.1, acc.2.2.1 i.1)) <$>
    foldlMList (simOutStep m I)
      (buildOutItems m k I outs accI.1 y_bits)
      (zeroStep3Acc m)

private theorem simOutStepProj_projStep2Acc {m k : ℕ} [NeZero m] (I : Finset (Fin m))
    (outs : List ℕ) (y_bits : Fin m → List Bool) (acc2 : Step2Acc m) :
    simOutStepProj m k I outs y_bits (projStep2Acc I acc2) =
      (fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        foldlMList (simOutStep m I)
          (buildOutItems m k I outs acc2.1 y_bits)
          (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []) := by
  rw [foldlMList_simOutStep_eq_map I _ (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []),
    Functor.map_map]
  rfl

private theorem eval_simSharedMulSteps_outputSteps_proj {m n k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (yI : (i : I) → BitString k)
    (cI aI : (i : I) → List Bool) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outputDist m k (GMWCircuit.extendByZero I yI)
      let res ← simSharedMulSteps I (GMWCircuit.outputSteps m n k D)
        (I.restrict w) (I.restrict r_out)
      return fun i : I =>
        (cI i ++
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).1,
         aI i ++
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).2,
         encOutCoordsMsgReceived i.1 (GMWCircuit.outCoords m k) (res i).2)) =
    ProbComp.eval
      (simOutStepProj m k I D.code.2
        (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩) else List.replicate k false)
        (fun s => wireToList (w s), cI, aI)) := by
  let c₂ : Fin m → List Bool := fun s => if hs : s ∈ I then cI ⟨s, hs⟩ else []
  let a₂ : Fin m → List Bool := fun s => if hs : s ∈ I then aI ⟨s, hs⟩ else []
  have hc (i : I) : cI i = c₂ i.1 := by simp [c₂, i.2]
  have ha (i : I) : aI i = a₂ i.1 := by simp [a₂, i.2]
  have hproj :
      (fun s => wireToList (w s), cI, aI) =
        projStep2Acc I (fun s => wireToList (w s), c₂, a₂) := by
    refine Prod.ext rfl (Prod.ext (funext hc) (funext ha))
  rw [hproj, simOutStepProj_projStep2Acc, ← eval_simSharedMulSteps_outputSteps]
  simp_rw [← hc, ← ha]

private def packSimOutputFromCoalition {m : ℕ} (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (q : (i : I) → List Bool × List Bool × List Bool) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i =>
      if hi : i ∈ I then
        encPair
          (encPair (encPair encBits encBits) (encPair encBits encBits))
          (encPair encBits (encPair encBits encBits))
          (((x_bits i, r_bits i), (c1_bits i, (q ⟨i, hi⟩).1)),
           (in_shares i, ((q ⟨i, hi⟩).2.1, (q ⟨i, hi⟩).2.2)))
      else [])

private theorem packSimOutputFromCoalition_eq_packSimOutput {m : ℕ} (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool) (acc3 : Step3Acc m) :
    packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares
      (fun i : I => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) =
    packSimOutput m I x_bits r_bits c1_bits in_shares acc3 := by
  simp only [packSimOutputFromCoalition, packSimOutput, packPartyViewWord, dite_eq_ite]

private theorem eval_simSharedMulSteps_gmwCircuitSim {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k))
    (I : Finset (Fin m))
    (xI : (i : I) → BitString n) (yI : (i : I) → BitString k)
    (rI : (i : I) → BitString coins)
    (c₁ : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) :
    let D := C.comp (xorPreludeCircuit m n coins)
    let xr : Fin m → BitString (n + coins) :=
      GMWCircuit.extendByZero I (fun i => Fin.append (xI i) (rI i))
    let y : Fin m → BitString k := GMWCircuit.extendByZero I yI
    let x_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (xI ⟨s, hs⟩) else List.replicate n false
    let r_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (rI ⟨s, hs⟩) else []
    let y_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (yI ⟨s, hs⟩) else List.replicate k false
    let c1_bits : Fin m → List Bool := fun s =>
      List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c₁ s))
    let in_shares := step1Wires m (n + coins) x_bits r_bits c1_bits
    ProbComp.eval (do
      let r_prog ← GMWCircuit.progDist m (Cslib.BitString.blocksEquiv.symm xr) D.program
      let r_out ← GMWCircuit.outputDist m k y
      let sub ← simSharedMulSteps I (gmwCircuitProtocol m (n + coins) k D).steps
        (fun i => (Fin.append (xI i) (rI i), c₁ i.1))
        (fun i =>
          Schedule.Received.append (GMWCircuit.deliverInputShares xr c₁ i.1)
            (Schedule.Received.append (r_prog i.1) (r_out i.1)))
      return encodeCoalitionView (encGMWPartyView m coins n k C) I
        (fun i =>
          ⟨xI i,
           (rI i, ((c₁ i.1, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i.1), (sub i).1)),
           (sub i).2⟩)) =
    ProbComp.eval (do
      let acc2 ← foldlMList (simGateStep m I) D.code.1 (in_shares, fun _ => [], fun _ => [])
      let outItems := buildOutItems m k I D.code.2 acc2.1 y_bits
      let acc3 ← foldlMList (simOutStep m I) outItems (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
      return packSimOutput m I x_bits r_bits c1_bits in_shares acc3) := by
  intro D xr y x_bits r_bits y_bits c1_bits in_shares
  let st : Fin m → BitString (m * (n + coins)) :=
    fun i => Cslib.BitString.blocksEquiv.symm
      (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i)
  have hst_in : (fun i => List.ofFn (st i)) = in_shares :=
    funext fun i => (step1Wires_sim_ofFn I xI rI c₁ i).symm
  have hst_sum (idx : Fin (m * (n + coins))) :
      (∑ i : Fin m, st i idx) = Cslib.BitString.blocksEquiv.symm xr idx := by
    have h := GMWCircuit.sum_outputAt_inputShareSteps xr c₁ idx
    simp only [GMWCircuit.outputAt_inputShareSteps] at h
    exact h
  have hstep1 :
      simSharedMulSteps I (GMWCircuit.inputShareSteps m (n + coins))
        (fun i => (Fin.append (xI i) (rI i), c₁ i.1))
        (fun i => GMWCircuit.deliverInputShares xr c₁ i.1) =
      pure (fun i : I =>
        (unitOTMsgSubCoins i.1 (GMWCircuit.allPairs m),
         receivedOTMsgScheduleOfInbox i.1
           (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i.1)
           (GMWCircuit.allPairs m))) :=
    simSharedMulSteps_inputShareSteps I _ _
  have hout1_at (i : I) :
      (GMWCircuit.inputShareSteps m (n + coins)).outputAt i.1
        (Fin.append (xI i) (rI i), c₁ i.1)
        (GMWCircuit.deliverInputShares xr c₁ i.1) =
      st i.1 := by
    have hxr_i : Fin.append (xI i) (rI i) = xr i.1 := by
      simp [xr, GMWCircuit.extendByZero, i.2]
    rw [hxr_i, GMWCircuit.outputAt_inputShareSteps]
  dsimp only [gmwCircuitProtocol]
  simp_rw [simSharedMulSteps_append, hstep1, pure_bind, hout1_at]
  have henc (r_prog : (i : Fin m) → (GMWCircuit.progSchedule m D.program).Received i)
      (sub₁ : (i : I) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.progSchedule m D.program)) i.1 ×
        (otMulCompose (GMWCircuit.progSchedule m D.program)).Received i.1)
      (sub₂ : (i : I) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.outputSchedule m k)) i.1 ×
        (otMulCompose (GMWCircuit.outputSchedule m k)).Received i.1) :
      encodeCoalitionView (encGMWPartyView m coins n k C) I
        (fun i =>
          ⟨xI i,
           (rI i,
            ((c₁ i.1, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i.1),
             joinOTSubCoins (GMWCircuit.inputShareSchedule m (n + coins))
               (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i.1
               (unitOTMsgSubCoins i.1 (GMWCircuit.allPairs m))
               (joinOTSubCoins (GMWCircuit.progSchedule m D.program)
                 (GMWCircuit.outputSchedule m k) i.1 (sub₁ i).1 (sub₂ i).1))),
           joinOTMulCompose (GMWCircuit.inputShareSchedule m (n + coins))
             (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i.1
             (receivedOTMsgScheduleOfInbox i.1
               (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i.1)
               (GMWCircuit.allPairs m))
             (joinOTMulCompose (GMWCircuit.progSchedule m D.program)
               (GMWCircuit.outputSchedule m k) i.1 (sub₁ i).2 (sub₂ i).2)⟩) =
      packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares
        (fun i : I =>
          (encOTSubCoins
             (Schedule.compose (fun _ => multiPartyMulSchedule m)
               (GMWCircuit.progSchedule m D.program))
             i.1 (sub₁ i).1 ++
             encOTSubCoins
               (Schedule.compose (fun _ => multiPartyMulSchedule m)
                 (GMWCircuit.outputSchedule m k))
               i.1 (sub₂ i).1,
           encOTOracleAnswers
             (Schedule.compose (fun _ => multiPartyMulSchedule m)
               (GMWCircuit.progSchedule m D.program))
             i.1 (sub₁ i).2 ++
             encOTOracleAnswers
               (Schedule.compose (fun _ => multiPartyMulSchedule m)
                 (GMWCircuit.outputSchedule m k))
               i.1 (sub₂ i).2,
           encOutCoordsMsgReceived i.1 (GMWCircuit.outCoords m k) (sub₂ i).2)) := by
    dsimp only [encodeCoalitionView, packSimOutputFromCoalition]
    refine congrArg (encList encBits) (List.map_congr_left fun i _ => ?_)
    by_cases hi : i ∈ I
    · simp only [hi, ↓reduceDIte]
      dsimp only [D]
      rw [encGMWPartyView_of_join, ← hst_in]
      simp [x_bits, r_bits, c1_bits, st, hi]
    · simp [hi]
  have hstep3 (r_prog : (i : Fin m) → (GMWCircuit.progSchedule m D.program).Received i)
      (sub₁ : (i : I) →
        Schedule.SubCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.progSchedule m D.program)) i.1 ×
        (otMulCompose (GMWCircuit.progSchedule m D.program)).Received i.1) :
      ProbComp.eval (do
        let r_out ← GMWCircuit.outputDist m k y
        let sub₂ ← simSharedMulSteps I (GMWCircuit.outputSteps m (n + coins) k D)
          (I.restrict fun s => (GMWCircuit.progSteps m D.program).outputAt s (st s) (r_prog s))
          (I.restrict r_out)
        return encodeCoalitionView (encGMWPartyView m coins n k C) I
          (fun i =>
            ⟨xI i,
             (rI i,
              ((c₁ i.1, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i.1),
               joinOTSubCoins (GMWCircuit.inputShareSchedule m (n + coins))
                 (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i.1
                 (unitOTMsgSubCoins i.1 (GMWCircuit.allPairs m))
                 (joinOTSubCoins (GMWCircuit.progSchedule m D.program)
                   (GMWCircuit.outputSchedule m k) i.1 (sub₁ i).1 (sub₂ i).1))),
             joinOTMulCompose (GMWCircuit.inputShareSchedule m (n + coins))
               (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i.1
               (receivedOTMsgScheduleOfInbox i.1
                 (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i.1)
                 (GMWCircuit.allPairs m))
               (joinOTMulCompose (GMWCircuit.progSchedule m D.program)
                 (GMWCircuit.outputSchedule m k) i.1 (sub₁ i).2 (sub₂ i).2)⟩)) =
      ProbComp.eval
        (packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares <$>
          simOutStepProj m k I D.code.2 y_bits
            (fun s => wireToList ((GMWCircuit.progSteps m D.program).outputAt s (st s) (r_prog s)),
             fun i : I => encOTSubCoins _ i.1 (sub₁ i).1,
             fun i : I => encOTOracleAnswers _ i.1 (sub₁ i).2)) := by
    simp_rw [henc r_prog sub₁]
    have hout := congrArg
      (PMF.map (packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares))
      (eval_simSharedMulSteps_outputSteps_proj I D
        (fun s => (GMWCircuit.progSteps m D.program).outputAt s (st s) (r_prog s)) yI
        (fun i : I => encOTSubCoins _ i.1 (sub₁ i).1)
        (fun i : I => encOTOracleAnswers _ i.1 (sub₁ i).2))
    simpa only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
      PMF.map_bind, PMF.map_comp, Function.comp_def, y, y_bits] using hout
  have hprog := congrArg
    (fun d =>
      d.bind fun accI =>
        ProbComp.eval
          (packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares <$>
            simOutStepProj m k I D.code.2 y_bits accI))
    (eval_simSharedMulSteps_progSteps I (Cslib.BitString.blocksEquiv.symm xr) D.program st hst_sum)
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, PMF.pure_bind, PMF.map_comp, Function.comp_def, hst_in,
    simOutStepProj_projStep2Acc, packSimOutputFromCoalition_eq_packSimOutput] at hprog
  simp only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine Eq.trans ?_ hprog
  refine congrArg (PMF.bind _) (funext fun r_prog => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun sub₁ => ?_)
  simpa only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
    PMF.map_comp, Function.comp_def, I.restrict_def] using hstep3 r_prog sub₁

private theorem eval_simRunWord_eq_gmwOT14RandomizedSim {α : Type} (m : ℕ) [NeZero m]
    (coins n k : α → ℕ)
    (C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a))
    (I : Finset (Fin m)) (inp : FamilySimInput α m n k I) :
    ProbComp.eval
      (simRunWord m coins n k
        (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code) I inp) =
    ProbComp.eval
      (encodeCoalitionView (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)) I <$>
        gmwOT14RandomizedSim m (coins inp.1) (n inp.1) (k inp.1) (C inp.1) I inp.2.1 inp.2.2) := by
  rcases inp with ⟨a, xI, yI⟩
  let D := (C a).comp (xorPreludeCircuit m (n a) (coins a))
  have hrhs (rI : (i : I) → BitString (coins a)) :
      (encodeCoalitionView (encGMWPartyView m (coins a) (n a) (k a) (C a)) I <$>
        ((fun v (i : I) =>
          (⟨xI i, (rI i, (v i).coins), (v i).received⟩ :
            PartyView (fun _ => BitString (n a)) _ _ i.1)) <$>
          mapInputSim
            (fun _ (xr : BitString (n a) × BitString (coins a)) => Fin.append xr.1 xr.2)
            (gmwOT14Sim m (n a + coins a) (k a) D) I
            (fun i => (xI i, rI i)) yI)) =
      (do
        let c₁ ← OracleComp.pi
          (fun _ : Fin m => ProbComp.uniform (Fin (n a + coins a) → Fin (m - 1) → Bool))
        let xr := GMWCircuit.extendByZero I (fun i => Fin.append (xI i) (rI i))
        let r_prog ← GMWCircuit.progDist m (Cslib.BitString.blocksEquiv.symm xr) D.program
        let r_out ← GMWCircuit.outputDist m (k a) (GMWCircuit.extendByZero I yI)
        let sub ← simSharedMulSteps I (gmwCircuitProtocol m (n a + coins a) (k a) D).steps
          (fun i => (Fin.append (xI i) (rI i), c₁ i.1))
          (fun i =>
            Schedule.Received.append (GMWCircuit.deliverInputShares xr c₁ i.1)
              (Schedule.Received.append (r_prog i.1) (r_out i.1)))
        return encodeCoalitionView (encGMWPartyView m (coins a) (n a) (k a) (C a)) I
          (fun i =>
            ⟨xI i,
             (rI i,
              ((c₁ i.1, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i.1),
               (sub i).1)),
             (sub i).2⟩)) := by
    simp only [mapInputSim, gmwOT14Sim, composeSim, gmwCircuitSim, GMWCircuit.gmwCircuitRealViews,
      expandSimSteps_twoPartyMulSim, simSharedMulSteps,
      bind_assoc, map_bind, bind_map_left, bind_pure_comp, map_pure, Functor.map_map,
      I.restrict_def]
    rfl
  rw [simRunWord, gmwOT14RandomizedSim, randomizedWrapperSim]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
    eval_sampleTwoPiBits_sim m (coins a) (n a + coins a) I,
    PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg (PMF.bind _) (funext fun rI => ?_)
  have hrhs_eval := congrArg ProbComp.eval (hrhs rI)
  simp only [D, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
    PMF.map_comp, Function.comp_def] at hrhs_eval
  rw [hrhs_eval]
  refine congrArg (PMF.bind _) (funext fun c₁ => ?_)
  simpa only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp] using
    (eval_simSharedMulSteps_gmwCircuitSim (C a) I xI yI rI c₁).symm

end PolyTimeRunner

/-! ### Part 5: Uniform Polynomial-Time Certificates and End-to-End Theorem 7.5.12 -/

open Turing.MultiTapeTM Cslib.Circuits

/-- Uniform oracle-PPT certificate for the centralized joint word-level runner `Protocol.runEncoded`
applied to the `m`-party $\text{OT}_1^4$-hybrid GMW protocol family `gmwOT14RandomizedProtocol`
(certifying the joint word-level execution across all `m` parties over `encFamilyRunInput enc m n`
rather than separate per-party local PPT strategies). -/
theorem isOraclePPTOn_gmwOT14RandomizedProtocol {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode) :
    Cslib.Probability.IsOraclePPTOn (encFamilyRunInput enc m n) encBits
      (fun inp =>
        (gmwOT14RandomizedProtocol m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)).runEncoded
          (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1))
          (fun _ y => List.ofFn y) inp.2) := by
  have hD := computableInPolyTime_code_comp_xorPreludeCircuit m hn hcoins hC
  exact (PolyTimeRunner.isOraclePPTOn_realRunWord m hcoins.tidy hn.tidy hk.tidy hD.tidy).congr
    (fun inp _ oracle s =>
      PolyTimeRunner.runWith_realRunWord_eq_runEncoded m coins n k C inp oracle s)

/-- Uniform PPT certificate for the `m`-party $\text{OT}_1^4$-hybrid GMW coalition simulator family
`gmwOT14RandomizedSim` for any static coalition `I : Finset (Fin m)`. -/
theorem isPPTOn_gmwOT14RandomizedSim {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode)
    (I : Finset (Fin m)) :
    Cslib.Probability.IsPPTOn (encFamilySimInput enc m n k I) encBits
      (fun inp =>
        encodeCoalitionView
          (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)) I <$>
          gmwOT14RandomizedSim m (coins inp.1) (n inp.1) (k inp.1)
            (C inp.1) I inp.2.1 inp.2.2) := by
  have hD := computableInPolyTime_code_comp_xorPreludeCircuit m hn hcoins hC
  exact (PolyTimeRunner.isPPTOn_simRunWord m I hcoins.tidy hn.tidy hk.tidy hD.tidy).congr
    (PolyTimeRunner.eval_simRunWord_eq_gmwOT14RandomizedSim m coins n k C I)

/-- Proper-coalition variant of Theorem 7.5.12 (Goldreich Section 7.5.2.4, p. 707; generalizing
Theorem 7.3.11, Section 7.3.4, p. 648): every polynomial-time `m`-party randomized functionality
family `F` is privately reducible to $\text{OT}_1^4$ in the semi-honest model against every proper
static coalition `I ≠ Finset.univ`, with uniform polynomial-time circuit family `C`, uniform
`IsOraclePPTOn` joint word-level protocol execution via `Protocol.runEncoded` (linked to
`Protocol.evalWith ot14World` by `Protocol.eval_runEncoded_eq_evalWith_map`), and uniform
`IsPPTOn` coalition simulators.

Note that the proper-coalition quantifier `I ≠ Finset.univ` (`PerfectSemiHonestPrivateProper`) is
narrower than Goldreich's Definition 7.5.1 and Theorem 7.5.12 (which quantify over all `I ⊆ [m]`,
p. 696; Goldreich's text on pp. 697 and 703 treats `I = [m]` as trivial without restricting that
remark to deterministic functionalities or to the view-only Eq. 7.39). Under the joint
view-and-output equation Eq. 7.40 for randomized functionalities, `I = Finset.univ` is not vacuous:
the canonical independent-coin-share simulator `randomizedWrapperSim` is refuted at
`I = Finset.univ` by `not_perfectSemiHonestPrivate_coinEchoRandomizedWrapper_univ` in
[ComplexityTests/Crypto/MPC.lean](https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/Crypto/MPC.lean),
and any full-coalition simulator receiving only `(x, y)` would have to sample coin shares whose
XOR `r` satisfies `g(r, x) = y`. -/
theorem exists_perfectSemiHonestPrivate_ot14_of_polyTime {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ} {F : α × List Bool → List Bool}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ∃ C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a),
      ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode ∧
      (∀ a (xr : Fin (m * n a + coins a) → Bool) (j : Fin (m * k a)),
        (C a).eval Boolean.interpretation xr j =
          (F (a, List.ofFn xr)).getD j.val false) ∧
      (∀ a, PerfectSemiHonestPrivateProper
        (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)) ot14World
        (wordRandomizedFunctionality m coins n k F a)
        (gmwOT14RandomizedSim m (coins a) (n a) (k a) (C a))) ∧
      Cslib.Probability.IsOraclePPTOn (encFamilyRunInput enc m n) encBits
        (fun inp =>
          (gmwOT14RandomizedProtocol m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)).runEncoded
            (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1))
            (fun _ y => List.ofFn y) inp.2) ∧
      (∀ (I : Finset (Fin m)), I ≠ Finset.univ →
        Cslib.Probability.IsPPTOn (encFamilySimInput enc m n k I) encBits
          (fun inp =>
            encodeCoalitionView
              (encGMWPartyView m (coins inp.1) (n inp.1) (k inp.1) (C inp.1)) I <$>
              gmwOT14RandomizedSim m (coins inp.1) (n inp.1) (k inp.1)
                (C inp.1) I inp.2.1 inp.2.2)) := by
  have h_in : ComputableInPolyTime (fun a => m * n a + coins a) enc encUnary := by
    have hmn := ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_mul
      ((ComputableTidilyInPolyTime.const m).prod hn.tidy)
    exact ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_add
        (hmn.prod hcoins.tidy))
  have h_out : ComputableInPolyTime (fun a => m * k a) enc encUnary := by
    have hmk := ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_mul
      ((ComputableTidilyInPolyTime.const m).prod hk.tidy)
    exact ComputableInPolyTime.of_tidy hmk
  obtain ⟨C, hC_code, hC_eval⟩ :=
    Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily h_in h_out hF
  refine ⟨C, hC_code, hC_eval, fun a => ?_,
    isOraclePPTOn_gmwOT14RandomizedProtocol m hcoins hn hk hC_code,
    fun I _ => isPPTOn_gmwOT14RandomizedSim m hcoins hn hk hC_code I⟩
  have hfunc :
      randomizedFunctionality (coins a) (fun r x i =>
        Cslib.BitString.block
          ((C a).eval Boolean.interpretation
            (Fin.append
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n a)).symm x) r)) i) =
      wordRandomizedFunctionality m coins n k F a := by
    unfold wordRandomizedFunctionality
    congr 1
    funext r x i j
    rw [Cslib.BitString.block, hC_eval a _ (finProdFinEquiv (i, j)), finProdFinEquiv_apply_val]
    dsimp only [encodeCoinsAndInputs]
    congr 1
    ring
  rw [← hfunc]
  exact perfectSemiHonestPrivateProper_gmwOT14Randomized m (coins a) (n a) (k a) (C a)

end Cslib.Crypto.Protocols.MPC
