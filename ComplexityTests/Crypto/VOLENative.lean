/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.VOLE.NativePPT
import Complexity.Foundations.Data.BitString.ZModTwo
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PPT

/-! Native clients charge growing lists and retain private coins across cached-share reads. -/

namespace ComplexityTests.Crypto.VOLENative

open Cslib Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
  Cslib.Crypto.Protocols.VOLE Cslib.Crypto.Protocols.VOLE.Native Turing.MultiTapeTM

abbrev State := Bool × Share Bool × List Bool
abbrev Result := State × Share Bool

def stateEncoding : State ↪ List Bool :=
  encPair encBool (encPair (encShare encBool) (encList encBool))

def resultEncoding : Result ↪ List Bool := encPair stateEncoding (encShare encBool)

noncomputable def receiver : Receiver Bool State Result where
  init _ share := do
    let coin ← ProbComp.uniform Bool
    return (coin, share, [])
  challenge input share state d := pure
    (List.replicate input.2.1.length
      (state.1 ^^ share.1 ^^ share.2.getD 0 false ^^ d.getD 0 false),
      (state.1, state.2.1, d))
  receive _ share state reply :=
    pure (state.1, state.2.1, [reply.1, reply.2, share.1] ++ share.2 ++ state.2.2)
  terminal _ share state := pure (state, share)

-- One native certificate covers every wire count and every encoded (even malformed) layout.
theorem receiver_simulator_ppt :
    IsPPTOn encInput (encView encBool resultEncoding)
      (simulate (ProbComp.uniform Bool) receiver) := by
  apply isPPTOn_simulate _ _ stateEncoding resultEncoding
  · exact isPPTOn_uniform_bool _
  · exact ComputableInPolyTime.of_finite _
  · exact ComputableInPolyTime.of_finite _
  · exact ComputableInPolyTime.of_finite _
  · unfold receiver stateEncoding encShare encInput
    ppt
  · unfold receiver stateEncoding encShare encInput
    ppt
  · unfold receiver stateEncoding encShare encInput
    ppt
  · unfold receiver resultEncoding stateEncoding encShare encInput
    ppt

-- The same program simulates every satisfying circuit, including noninjective wire maps.
example {n m : ℕ} (left right output : Fin m → Fin n) (w : Fin n → Bool)
    (hw : ∀ i, w (left i) * w (right i) = w (output i)) (z : List Bool) :
    (maskedMulCheckReceiverView left right output (receiver.strategy n m) w
      (inputOfMaps left right output z)).map viewToLists =
        ProbComp.eval (simulate (ProbComp.uniform Bool) receiver
          (inputOfMaps left right output z)) :=
  receiverView_eq_eval_simulate _ _ _ _ (ProbComp.eval_uniform _) _ _ _ hw

example (m : ℕ) (z : List Bool) :
    (maskedMulCheckReceiverView (fun _ : Fin m => (0 : Fin 1)) (fun _ => 0) (fun _ => 0)
      (receiver.strategy 1 m) (fun _ => true)
      (inputOfMaps (fun _ : Fin m => (0 : Fin 1)) (fun _ => 0) (fun _ => 0) z)).map viewToLists =
      ProbComp.eval (simulate (ProbComp.uniform Bool) receiver
        (1, List.replicate m (0, 0, 0), z)) := by
  simpa [inputOfMaps] using receiverView_eq_eval_simulate
    (fun _ : Fin m => (0 : Fin 1)) (fun _ => 0) (fun _ => 0)
    (ProbComp.uniform Bool) (ProbComp.eval_uniform _) receiver z (fun _ => true) (fun _ => rfl)

example :
    (maskedMulCheckReceiverView (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0 Fin.elim0
      (receiver.strategy 0 0) Fin.elim0 (0, [], [])).map viewToLists =
      ProbComp.eval (simulate (ProbComp.uniform Bool) receiver (0, [], [])) := by
  simpa [inputOfMaps] using receiverView_eq_eval_simulate
    (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0 Fin.elim0 (ProbComp.uniform Bool)
    (ProbComp.eval_uniform _) receiver [] Fin.elim0 (fun i => Fin.elim0 i)

-- Both short and long callback replies are normalized into the actual transmitted vector.
example : weights 3 [true] = [true, false, false] ∧
    weights 1 [false, true] = [false] := by decide

-- A huge binary gate index uses the default, rather than requiring that many wires.
example : checkValue (1, [(2 ^ 100, 0, 0)], [])
    (true, [true, false]) [false] [true] = true := by decide

-- The private coin, receiver key, raw tag and correction all affect the chosen weight.
example :
    receiver.challenge (1, [(0, 0, 0)], []) (false, []) (false, (false, []), []) [false] ≠
      receiver.challenge (1, [(0, 0, 0)], []) (false, []) (true, (false, []), []) [false] := by
  simp [receiver]

-- Every run retains the initial coin and share while the terminal phase reads the cache again.
example (input : Input) (view : View Bool Result)
    (hv : view ∈ (ProbComp.eval (simulate (ProbComp.uniform Bool) receiver input)).support) :
    view.2.2.2.2.1.2.1 = view.1 ∧ view.2.2.2.2.2 = view.1 ∧
      view.2.2.2.2.1.2.2 = [view.2.2.2.1.1, view.2.2.2.1.2, view.1.1] ++
        view.1.2 ++ view.2.1 ∧
      view.2.2.1 = List.replicate input.2.1.length
        (view.2.2.2.2.1.1 ^^ view.1.1 ^^ view.1.2.getD 0 false ^^ view.2.1.getD 0 false) := by
  simp only [simulate, receiver, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hv
  rcases hv with ⟨delta, _, q, _, state, ⟨coin, _, rfl⟩, d, _, chosen, rfl,
    a, _, processed, rfl, result, rfl, rfl⟩
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply List.ext_getElem (by simp [weights])
  intro i hi hi'
  have hi0 : i < input.2.1.length := by
    simpa only [weights, List.length_map, List.length_range] using hi
  simp [weights, hi0]

def constantReceiver : Receiver Bool Unit Unit where
  init _ _ := pure ()
  challenge _ _ _ _ := pure ([true], ())
  receive _ _ _ _ := pure ()
  terminal _ _ _ := pure ()

private def leftWire : Fin 1 → Fin 2 := fun _ => 0
private def outWire : Fin 1 → Fin 2 := fun _ => 1
private def falseWitness : Fin 2 → Bool := ![true, false]
private def falseView :
    (Bool × (Fin 3 → Bool)) × Transcript (maskedMulCheckSpec Bool (Fin 1) 2) × Unit :=
  ((true, fun _ => false), (falseWitness, (fun _ => true), (false, false), ()), ())

private theorem falseView_real : falseView ∈
    (maskedMulCheckReceiverView leftWire leftWire outWire (constantReceiver.strategy 2 1)
      falseWitness (inputOfMaps leftWire leftWire outWire [])).support := by
  have hrun : maskedMulCheckReceiverView leftWire leftWire outWire
      (constantReceiver.strategy 2 1) falseWitness
      (inputOfMaps leftWire leftWire outWire []) = (voleIdealDist Bool 3).map (fun c =>
        (c.receiverView, (voleCommitWitness falseWitness (Fin.init c.u), (fun _ => true),
          maskedMulCheckReply leftWire leftWire outWire falseWitness c.u c.v (fun _ => true),
            ()), ())) := by
    simp [maskedMulCheckReceiverView, Receiver.strategy, constantReceiver, World.eval, voleWorld,
      maskedMulCheck, liftProver, liftVerifier, runAgainst, ProverStrategy.hoist,
      VerifierStrategy.hoist, maskedMulCheckSpec, Cslib.Crypto.Protocols.SigmaProtocol.sigmaSpec,
      ProbOracleComp.query, ProbOracleComp.sample, ProbOracleComp.runWith,
      OracleComp.sumHandler, VOLECorrelation.senderView, PMF.map, Function.comp_def, PMF.bind_bind]
  rw [hrun]
  refine (PMF.mem_support_map_iff _ _ _).mpr ⟨voleSample (fun _ => false) (fun _ => false) true,
    (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _), ?_⟩
  decide

-- Encoding retains the distinguishing rejecting transcript of a false multiplication witness.
example :
    (maskedMulCheckReceiverView leftWire leftWire outWire (constantReceiver.strategy 2 1)
      falseWitness (inputOfMaps leftWire leftWire outWire [])).map viewToLists ≠
      ProbComp.eval (simulate (ProbComp.uniform Bool) constantReceiver
        (inputOfMaps leftWire leftWire outWire [])) := by
  intro heq
  rw [eval_simulate _ _ _ _ (ProbComp.eval_uniform _)] at heq
  have hinj : Function.Injective
      (viewToLists (F := Bool) (Result := Unit) (n := 2) (m := 1)) := by
    rintro ⟨⟨delta, q⟩, ⟨d, r, reply, ⟨⟩⟩, ⟨⟩⟩
      ⟨⟨delta', q'⟩, ⟨d', r', reply', ⟨⟩⟩, ⟨⟩⟩ h
    simpa only [viewToLists, Prod.mk.injEq, List.ofFn_inj, and_true] using h
  have hv := falseView_real
  rw [PMF.map_injective hinj heq] at hv
  have hcheck := maskedMulCheckReceiverSimulate_accepts leftWire leftWire outWire
    (constantReceiver.strategy 2 1) (inputOfMaps leftWire leftWire outWire []) hv
  have hfalse : ¬ (maskedMulCheckValue leftWire leftWire outWire falseView.1.1 falseView.1.2
      falseView.2.1.1 falseView.2.1.2.1 =
        falseView.2.1.2.2.1.1 * falseView.1.1 + falseView.2.1.2.2.1.2) := by decide
  exact hfalse hcheck

end ComplexityTests.Crypto.VOLENative
