/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.PolyTime.Runner
-- `import all`: the runner equivalence proofs unfold the private word-level runners and
-- encoders of `Runner` and `Encoding` (e.g. `realGateStep`, `simGateStep`, `Step2Acc`,
-- `encOTSubCoins`, `otMulCompose`).
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.Encoding
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.Runner
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Computability.Probabilistic.Finite
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Equivalence of the Word-Level GMW Runners: Input Sharing and Gates

Proof infrastructure for `Cslib.Crypto.Protocols.MPC.PolyTime`. It relates the word-level
runners of `Cslib.Crypto.Protocols.MPC.PolyTime.Runner` to `Protocol.runEncoded` and
`gmwOT14RandomizedSim` on Step 1 (`inputShareSteps`) and Step 2 (`progSteps`): one
`sharedMulSpec m` round expands into pairwise `ot14Spec` calls, and the word-level accumulators
track the typed received messages. Every declaration here is private;
`Cslib.Crypto.Protocols.MPC.PolyTime.Certificates` reads them through `import all`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3 (Construction 7.3.7, pp. 643–644),
  Section 7.3.4 (Theorem 7.3.11, p. 648), Section 7.5.1.2 (Definition 7.5.1, Eqs. 7.39–7.40,
  p. 696; p. 697), Section 7.5.2.1 (p. 703), Section 7.5.2.2 (Construction 7.5.8, p. 704),
  Section 7.5.2.3 (Construction 7.5.10, p. 706), and Section 7.5.2.4 (Theorem 7.5.12, p. 707).
-/

-- This proof-only stage is intentionally private; later stages import all.
set_option linter.privateModule false

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits Turing.MultiTapeTM

namespace PolyTimeRunner

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

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
      dsimp only [List.cons_append, joinSubCoins2, encOTSubCoins]
      rw [ih c_tail, List.append_assoc]

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
      dsimp only [List.cons_append, joinReceived2, encOTOracleAnswers]
      rw [ih r_tail, List.append_assoc]

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
    dsimp only [pairsSchedule, pairRound, List.map, List.append, Round.embed,
      splitPairsOTReceived, joinPairsOTReceived] at ih ⊢
    rw [ih r_tail]

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
      dsimp only [List.cons_append, splitOTMulCompose, joinOTMulCompose]
      rw [ih r_tail r_b]
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
    dsimp only [Steps.append, runOTSteps, joinSubCoins2, joinReceived2]
    simp [runOTSteps_mapState]
  | message send next ih =>
    dsimp only [Steps.append, List.append_eq, List.cons_append, runOTSteps,
      joinSubCoins2, joinReceived2] at ih ⊢
    simp only [bind_assoc, pure_bind, ih]
  | @oracle _ _ op _ _ query next ih =>
    cases op
    dsimp only [Steps.append, List.append_eq, List.cons_append, runOTSteps,
      joinSubCoins2, joinReceived2] at ih ⊢
    simp only [bind_assoc, pure_bind, ih]
    rfl

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
    rw [ProbOracleComp.runWith_sample_bind_congr oracle hpi]
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
    have hih := congrArg (PMF.map (Prod.map f id))
      (ih (fun i => (st i, Round.deliverMessage (send (st s₀)) i)) s)
    rw [← ProbOracleComp.runWith_map, ← ProbOracleComp.runWith_map] at hih
    simp only [f, Composition.Steps.compose, Composition.sampleSubCoins, Steps.runEncoded,
      Steps.runEncoded_mapState, Steps.outputAt, Steps.outputAt_mapState, runOTSteps,
      map_bind, Functor.map_map, bind_pure_comp] at hih ⊢
    exact hih
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
      simp only [pmf_norm, Composition.sampleSubCoins, eval_pi_pair,
        Composition.eval_pi_sampleSlotCoins, eval_pi_twoPartyMulCoins, ProbComp.eval_uniform]
    rw [ProbOracleComp.runWith_sample_bind_congr oracle hpi, ProbOracleComp.sample_bind,
      bind_assoc]
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
    rw [ProbOracleComp.runWith_sample_bind_comm, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_bind]
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
    dsimp only [runSharedMulSteps, Composition.Steps.compose, unitSubCoins, runOTSteps,
      joinOTSubCoins, joinOTMulCompose]
    simp
  | message send next ih =>
    dsimp only [Steps.append, List.append_eq, List.cons_append, runSharedMulSteps,
      Composition.Steps.compose, unitSubCoins, runOTSteps,
      joinOTSubCoins, joinOTMulCompose] at ih ⊢
    simp only [runOTSteps_mapState, bind_assoc, pure_bind] at ih ⊢
    rw [ih]
    simp
  | @oracle _ _ op parties rest query next ih =>
    cases op
    dsimp only [Steps.append, List.append_eq, List.cons_append, runSharedMulSteps,
      Composition.Steps.compose, unitSubCoins, joinOTSubCoins, joinOTMulCompose] at ih ⊢
    simp only [runOTSteps_append, runOTSteps_mapState, bind_assoc] at ih ⊢
    conv_lhs => arg 1; rw [runOTSteps_embed]
    conv_rhs => arg 1; rw [runOTSteps_embed]
    simp only [bind_map_left]
    refine congrArg (Bind.bind _) (funext fun res_embed => ?_)
    have hih := ih steps₂ (fun i => (st i, (res_embed.2.2 i).2))
    rw [hih]
    simp only [bind_assoc, pure_bind,
      joinPairsOTSubCoins_joinSubCoins2, joinPairsOTReceived_joinReceived2]

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
      dsimp only [List.cons_append, detExpandOTSim, Schedule.Received.append,
        joinSubCoins2, joinReceived2]
      rw [Prod.mk.injEq] at hih
      rw [hih.1, hih.2]
    | oracle op parties =>
      cases op
      dsimp only [List.cons_append, detExpandOTSim, Schedule.Received.append,
        joinSubCoins2, joinReceived2]
      rw [Prod.mk.injEq] at hih
      rw [hih.1, hih.2]

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
    dsimp only [Steps.outputAt, joinOTSubCoins, joinOTMulCompose]
    simp
  | message send next ih =>
    dsimp only [Steps.append, List.append_eq, List.cons_append, Schedule.Received.append,
      Steps.outputAt, joinOTSubCoins, joinOTMulCompose]
    simp only [simSharedMulSteps_message, ih,
      map_bind, bind_map_left, Functor.map_map, bind_pure_comp]
  | @oracle _ _ op parties rest query next ih =>
    cases op
    dsimp only [Steps.append, List.append_eq, List.cons_append, Schedule.Received.append,
      Steps.outputAt, joinOTSubCoins, joinOTMulCompose]
    simp only [simSharedMulSteps_oracle, ih,
      bind_assoc, map_bind, bind_map_left, Functor.map_map, bind_pure_comp,
      joinPairsOTSubCoins_joinSubCoins2, joinPairsOTReceived_joinReceived2]

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

private theorem map_update_of_not_mem {α β γ : Type} [DecidableEq α]
    {L : List α} {p : α} (hp : p ∉ L) (tr : α → β) (v : β) (g : α → β → γ) :
    (L.map fun q => g q (Function.update tr p v q)) = L.map fun q => g q (tr q) :=
  List.map_congr_left fun q hq => by rw [Function.update_of_ne (fun h : q = p => hp (h ▸ hq))]

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
      refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
      · dsimp only [post, acc', List.map_cons, List.sum_cons]
        rw [Function.update_self,
          map_update_of_not_mem hp tr _
            (fun q u => if q.1.1 = i then u.1 else if q.1.2 = i then u.2 else 0),
          add_assoc]
      · dsimp only [post, List.map_cons, List.flatten_cons]
        rw [Function.update_self,
          map_update_of_not_mem hp tr _ (fun q u => if q.1.1 = i then [u.1] else [])]
      · dsimp only [post, List.map_cons, List.flatten_cons]
        rw [Function.update_self,
          map_update_of_not_mem hp tr _ (fun q u => if q.1.2 = i then [u.2] else [])]

private theorem runSharedMulSteps_oracle_done {m : ℕ} {S β : Type} {Out : Fin m → Type}
    (g : ((i : Fin m) → Out i) → (Fin m → List Bool) → (Fin m → List Bool) → β)
    (query : (s : Fin m) → S → Bool × Bool)
    (finish : (i : Fin m) → S → Bool → Out i)
    (st : Fin m → S) :
    ((fun res =>
      g res.2.2
        (fun i =>
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
            i (res.1 i))
        (fun i =>
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
      g (fun i => finish i (st i) (mul.1 i)) mul.2.1 mul.2.2) <$>
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
  let post (t : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) : β :=
    g (fun i => finish i (st i) (t.1 i)) t.2.1 t.2.2
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
  dsimp only [Schedule.compose, List.append_nil, post, Function.comp_def]
  refine congrArg₂ (g _) (funext fun i => ?_) (funext fun i => ?_)
  · rw [encOTSubCoins_joinSubCoins2, encOTSubCoins_nil, List.append_nil]
  · rw [encOTOracleAnswers_joinReceived2, encOTOracleAnswers_nil, List.append_nil]

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

private theorem simSharedMulSteps_oracle_done {m : ℕ} [NeZero m] {S β : Type} {Out : Fin m → Type}
    (I : Finset (Fin m))
    (g : ((i : I) → List Bool × List Bool) → β)
    (query : (s : Fin m) → S → Bool × Bool)
    (output : (i : Fin m) →
      (S ×
        (Round.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))).Received i) →
      Out i)
    (stI : (i : I) → S)
    (x : Fin m → Bool × Bool) (hx : ∀ i : I, query i.1 (stI i) = x i.1)
    (ans : Fin m → Bool) :
    ((fun res =>
      g (fun i : I =>
        (encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          i.1 (res i).1,
         encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          i.1 (res i).2))) <$>
      simSharedMulSteps (State := fun _ => S) I
        (.oracle (spec := sharedMulSpec m) (op := ())
          (parties := Function.Embedding.refl (Fin m))
          query (.done output))
        stI
        (fun i =>
          (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
            (Function.Embedding.refl (Fin m)) ans i.1, ()))) =
    (fun r =>
      g (fun i : I =>
        ((simSharedMulPure m I x ans r).1 i.1,
         (simSharedMulPure m I x ans r).2 i.1))) <$>
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
    (funext fun r => congrArg g (funext fun i => ?_))
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

/-- Unit subcoins for party `i` along `msgSchedule Msg L` under `otMulCompose`. -/
private def unitOTMsgSubCoins {m : ℕ} {Msg : Type} (i : Fin m) :
    (L : List (Fin m × Fin m)) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (msgSchedule (spec := sharedMulSpec m) Msg L)) i
  | [] => ()
  | _ :: L => unitOTMsgSubCoins i L

/-- Received transcript for party `i` along `otMulCompose (msgSchedule Msg L)`
constructed from `inbox_i`. -/
private def receivedOTMsgScheduleOfInbox {m : ℕ} {Msg : Type}
    (i : Fin m) (inbox_i : Fin m → Msg) :
    (L : List (Fin m × Fin m)) →
      (otMulCompose (msgSchedule (spec := sharedMulSpec m) Msg L)).Received i
  | [] => ()
  | p :: L =>
    (receivedMsgOfInbox (spec := ot14Spec) p i inbox_i,
     receivedOTMsgScheduleOfInbox i inbox_i L)

@[simp] private theorem encOTSubCoins_msgSchedule {m : ℕ} {Msg : Type}
    (L : List (Fin m × Fin m)) (i : Fin m)
    (c : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (msgSchedule (spec := sharedMulSpec m) Msg L)) i) :
    encOTSubCoins
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (msgSchedule (spec := sharedMulSpec m) Msg L)) i c = [] := by
  induction L with
  | nil => rfl
  | cons _ _ ih => exact ih c

@[simp] private theorem encOTOracleAnswers_msgSchedule {m : ℕ} {Msg : Type}
    (L : List (Fin m × Fin m)) (i : Fin m)
    (r : (otMulCompose (msgSchedule (spec := sharedMulSpec m) Msg L)).Received i) :
    encOTOracleAnswers
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (msgSchedule (spec := sharedMulSpec m) Msg L)) i r = [] := by
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
    {State Out : Fin m → Type} (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (st : (i : Fin m) → State i × (Fin m → Msg)) :
    runSharedMulSteps (msgStepsWith (spec := sharedMulSpec m) send finish L) st =
      pure (fun i => unitOTMsgSubCoins i L,
        fun i => receivedOTMsgScheduleOfInbox i (fun s => send s (st s).1 i) L,
        fun i => (msgStepsWith (spec := sharedMulSpec m) send finish L).outputAt i (st i)
          (receivedScheduleOfInbox (spec := sharedMulSpec m) i
            (fun s => send s (st s).1 i) L)) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp only [msgStepsWith, runSharedMulSteps_message, runSharedMulSteps_mapState,
      ih, pure_bind, deliverMessage_eq_receivedMsgOfInbox (fun s => send s (st s).1) p,
      receivedScheduleOfInbox, receivedOTMsgScheduleOfInbox, unitOTMsgSubCoins,
      Steps.outputAt, Steps.outputAt_mapState]
    rfl

private theorem runSharedMulSteps_inputShareSteps {m N : ℕ}
    (xr : Fin m → BitString N) (c : Fin m → Fin N → Fin (m - 1) → Bool) :
    runSharedMulSteps (GMWCircuit.inputShareSteps m N) (fun i => (xr i, c i)) =
      pure (fun i => unitOTMsgSubCoins i (allPairs m),
        fun i => receivedOTMsgScheduleOfInbox i
          (fun s => GMWCircuit.shareInputBits m N (xr s) (c s) i) (allPairs m),
        fun i => Cslib.BitString.blocksEquiv.symm
          (fun s => GMWCircuit.shareInputBits m N (xr s) (c s) i)) := by
  simp only [GMWCircuit.inputShareSteps, allToAllStepsWith,
    runSharedMulSteps_mapState, runSharedMulSteps_msgStepsWith]
  congr 1
  refine Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))
  have hout := GMWCircuit.outputAt_inputShareSteps xr c i
  simpa only [GMWCircuit.inputShareSteps, allToAllStepsWith,
    GMWCircuit.deliverInputShares, Steps.outputAt_mapState] using hout

private theorem simSharedMulSteps_msgStepsWith {m : ℕ} [NeZero m] {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (I : Finset (Fin m))
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m))
    (stI : (i : I) → State i.1 × (Fin m → Msg))
    (inboxI : (i : I) → Fin m → Msg) :
    simSharedMulSteps I (msgStepsWith (spec := sharedMulSpec m) send finish L) stI
      (fun i => receivedScheduleOfInbox (spec := sharedMulSpec m) i.1 (inboxI i) L) =
    pure (fun i =>
      (unitOTMsgSubCoins i.1 L, receivedOTMsgScheduleOfInbox i.1 (inboxI i) L)) := by
  induction L generalizing stI with
  | nil => rfl
  | cons p L ih =>
    simp only [msgStepsWith, receivedScheduleOfInbox,
      receivedOTMsgScheduleOfInbox, unitOTMsgSubCoins,
      simSharedMulSteps_message, simSharedMulSteps_mapState, ih, map_pure]
    rfl

private theorem simSharedMulSteps_inputShareSteps {m N : ℕ} [NeZero m]
    (I : Finset (Fin m))
    (stI : (i : I) → BitString N × (Fin N → Fin (m - 1) → Bool))
    (inboxI : (i : I) → Fin m → BitString N) :
    simSharedMulSteps I (GMWCircuit.inputShareSteps m N) stI
      (fun i =>
        receivedScheduleOfInbox (spec := sharedMulSpec m) i.1 (inboxI i)
          (allPairs m)) =
    pure (fun i =>
      (unitOTMsgSubCoins i.1 (allPairs m),
       receivedOTMsgScheduleOfInbox i.1 (inboxI i) (allPairs m))) := by
  simp only [GMWCircuit.inputShareSteps, allToAllStepsWith,
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
      (if h : i = r then List.ofFn (receivedMsgOfInbox (s, r) i inbox_i h) else []) ++
        encPairsMsgReceived i (R.map fun r => (s, r))
          (receivedOTMsgScheduleOfInbox i inbox_i (R.map fun r => (s, r))) =
      (if i = r then List.ofFn (inbox_i s) else []) ++
        (R.map fun r => if i = r then List.ofFn (inbox_i s) else []).flatten
    rw [ih]
    by_cases h : i = r <;> simp [h, receivedMsgOfInbox]

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
    encPairsMsgReceived i (allPairs m)
      (receivedOTMsgScheduleOfInbox i inbox_i (allPairs m)) =
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
  rw [allPairs, hS, Cslib.BitString.ofFn_blocksEquiv_symm, List.ofFn_eq_map]

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
  rw [← List.ofFn_fin_append (x s) (r s), step1SenderShare_ofFn]

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

private theorem extractGateCoreInput_of_getD {m n g : ℕ} (op : Boolean.Op) (idxs : List ℕ)
    (w₀ w₁ : Wire n g) (h0 : idxs.getD 0 0 = w₀.toNat) (h1 : idxs.getD 1 0 = w₁.toNat)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    extractGateCoreInput m ((op, idxs), (fun i => wireToList (w i), c, a)) =
      (op, fun s => (w s w₀, w s w₁)) := by
  refine Prod.ext rfl (funext fun s => Prod.ext ?_ ?_)
  · dsimp only [extractGateCoreInput]; rw [h0]; exact getD_wireToList_toNat (w s) w₀
  · dsimp only [extractGateCoreInput]; rw [h1]; exact getD_wireToList_toNat (w s) w₁

@[simp] private theorem extractGateCoreInput_and {m n g : ℕ}
    (wires : Fin (Boolean.signature.Arity Boolean.Op.and) → Wire n g)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    extractGateCoreInput m
      (Line.code (σ := Boolean.signature) ⟨.and, wires⟩, (fun i => wireToList (w i), c, a)) =
      (.and, fun s => (w s (wires 0), w s (wires 1))) :=
  extractGateCoreInput_of_getD .and _ (wires 0) (wires 1) rfl rfl w c a

@[simp] private theorem extractGateCoreInput_or {m n g : ℕ}
    (wires : Fin (Boolean.signature.Arity Boolean.Op.or) → Wire n g)
    (w : Fin m → Wire n g → Bool) (c a : Fin m → List Bool) :
    extractGateCoreInput m
      (Line.code (σ := Boolean.signature) ⟨.or, wires⟩, (fun i => wireToList (w i), c, a)) =
      (.or, fun s => (w s (wires 0), w s (wires 1))) :=
  extractGateCoreInput_of_getD .or (Line.code (σ := Boolean.signature) ⟨.or, wires⟩).2
    (wires 0) (wires 1) rfl rfl w c a

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
    dsimp only [GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    refine (runSharedMulSteps_oracle_done
      (fun out c a => (fun i => wireToList (out i), fun i => c₁ i ++ c i, fun i => a₁ i ++ a i))
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ w_i bit => GMWCircuit.extendWire bit w_i) w).trans ?_
    rw [realGateStep, extractGateCoreInput_and, realGateCore, Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
    simp [finishMulGate, appendStep2Acc]
  | or =>
    dsimp only [GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    refine (runSharedMulSteps_oracle_done
      (fun out c a => (fun i => wireToList (out i), fun i => c₁ i ++ c i, fun i => a₁ i ++ a i))
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1)))
      (fun _ w_i bit => GMWCircuit.extendWire (w_i (wires 0) + w_i (wires 1) + bit) w_i)
      w).trans ?_
    rw [realGateStep, extractGateCoreInput_or, realGateCore, Functor.map_map]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
    simp [finishMulGate, appendStep2Acc]

private theorem runSharedMulSteps_progSteps {m n g : ℕ} [NeZero m]
    (prog : Program Boolean.signature n g)
    (st : Fin m → Fin n → Bool) :
    packStep2 <$> runSharedMulSteps (GMWCircuit.progSteps m prog) st =
      List.foldlM (flip (realGateStep m))
        (fun i => List.ofFn (st i), fun _ => [], fun _ => []) prog.code := by
  induction prog with
  | empty =>
    simp [GMWCircuit.progSteps, GMWCircuit.progSchedule, packStep2,
      encOTSubCoins_nil, encOTOracleAnswers_nil]
  | gate p line ih =>
    rw [GMWCircuit.progSteps, Program.code_gate, List.foldlM_append, ← ih]
    simp only [runSharedMulSteps_append, map_bind, bind_map_left, bind_pure_comp,
      List.foldlM_cons, flip.eq_def, List.foldlM_nil, bind_pure, Functor.map_map]
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
  | and | or =>
    dsimp only [GMWCircuit.lineDist, GMWCircuit.lineSteps, GMWCircuit.lineSchedule]
    rw [← hw (wires 0), ← hw (wires 1), simGateStepProj]
    simp only [extractGateCoreInput_and, extractGateCoreInput_or, simGateCore, simMulCore,
      bind_map_left, map_bind, bind_pure_comp, Functor.map_map, I.restrict_def,
      GMWCircuit.deliverMulOracle]
    refine congrArg (Bind.bind _) (funext fun ans => ?_)
    refine (simSharedMulSteps_oracle_done I
      (fun pair =>
        (_,
         fun i : I => cI i ++ (pair i).1,
         fun i : I => aI i ++ (pair i).2))
      (fun _ (w_s : Wire n g → Bool) => (w_s (wires 0), w_s (wires 1))) _
      (fun i => w i.1)
      (fun s => (w s (wires 0), w s (wires 1)))
      (fun _ => rfl) ans).trans ?_
    refine congrArg (Functor.map (f := ProbComp) · _) (funext fun r => ?_)
    simp [Steps.outputAt, Round.deliverOracle, finishMulGate]

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
      List.foldlM (flip (simGateStep m I))
        (fun i => List.ofFn (st i), fun _ => [], fun _ => []) prog.code) := by
  induction prog with
  | empty =>
    simp [GMWCircuit.progDist, GMWCircuit.progSteps, GMWCircuit.progSchedule,
      Steps.outputAt, encOTSubCoins_nil, encOTOracleAnswers_nil, projStep2Acc, I.restrict_def]
  | gate p line ih =>
    have hsum_p := (GMWCircuit.evalWith_progSteps x_flat p st hst).2
    rw [Program.code_gate, List.foldlM_append]
    simp only [List.foldlM_cons, flip.eq_def, List.foldlM_nil, bind_pure, map_bind,
      map_projStep2Acc_simGateStep]
    have hih := congrArg
      (PMF.bind · (fun accI => ProbComp.eval (simGateStepProj m I line.code accI))) ih.symm
    simp only [pmf_norm] at hih ⊢
    rw [hih]
    simp only [pmf_norm, GMWCircuit.progDist, GMWCircuit.progSteps, GMWCircuit.progSchedule,
      I.restrict_def, simSharedMulSteps_append, Steps.outputAt_append, bind_pure_comp]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r_p hr_p => ?_
    have hw := hsum_p r_p hr_p
    pmf_swap with sub₁
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

end PolyTimeRunner

end Cslib.Crypto.Protocols.MPC
