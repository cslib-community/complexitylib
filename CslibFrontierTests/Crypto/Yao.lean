/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontierTests.Crypto.MPC
import CslibFrontier.Crypto.Protocols.MPC.Yao
import Cslib.Computability.Circuit.Boolean.Basic

/-! # Yao's protocol and the semi-honest advantage: checked instances

* `semiHonestAdvantage`: zero for the perfectly private XOR protocol of
  `CslibFrontierTests.Crypto.MPC`, and positive for some distinguisher for every simulator of its
  leaky
  protocol.
* Yao's protocol for a one-gate AND circuit with the garbler's bit as input `0` and the evaluator's
  bit as input `1`, garbled with one-bit keys: the evaluator's decoding by computation on every
  input; the correctness theorem; perfect privacy against the garbler; and the evaluator bound with
  injective tweaks (`id`), which checks that its hypothesis is satisfiable. -/

namespace CslibFrontierTests.Crypto.Yao

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC
open CslibFrontierTests.Crypto.MPC

/-! ### The semi-honest advantage -/

-- Perfect privacy gives advantage zero against every distinguisher.
example (I : Finset (Fin 2)) (x : Fin 2 → Bool)
    (D : ((i : I) → PartyView (fun _ => Bool) (fun _ => Unit) xorSchedule i) × (Fin 2 → Bool) →
      ProbComp Bool) :
    semiHonestAdvantage xorProtocol noOracleWorld (Functionality.ofDeterministic xorFunc) I
      (xorSim I) x D = 0 :=
  perfectSemiHonestPrivate_xorProtocol.semiHonestAdvantage_eq_zero I x D

-- Against every simulator for the leaky protocol, some coalition, input and distinguisher have
-- positive advantage.
example (S : (I : Finset (Fin 2)) →
      CoalitionSimulator leakySchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) I) :
    ∃ I x D, semiHonestAdvantage leakyProtocol noOracleWorld
      (Functionality.ofDeterministic constFalseFunc) I (S I) x D ≠ 0 := by
  by_contra h
  exact not_perfectSemiHonestPrivate_leakyProtocol S fun I x =>
    (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mp fun D =>
      not_not.mp fun hD => h ⟨I, x, D, hD⟩

/-! ### Yao's protocol for one AND gate -/

/-- `x₀ ∧ x₁`, with `x₀` the garbler's bit and `x₁` the evaluator's. -/
def andC : Circuit Boolean.signature (1 + 1) 1 :=
  ⟨Program.empty.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩

/-- A toy keyed function on one-bit keys: the mask is the key, with the tweak ignored. It is not
pseudorandom; it only makes the statements concrete. -/
def toyF (k : Bool) (_ : Slot andC.topology) : Bool × Bool := (k, k)

/-- Fixed wire keys. -/
def toyKey : Wire (1 + 1) andC.size × Bool → Bool := fun p => p.2 || decide (p.1 = Wire.input 1)

/-- Fixed permutation bits. -/
def toyPerm : Wire (1 + 1) andC.size → Bool := fun w => decide (w = Wire.input 0)

-- The evaluator decodes the garbler's message and its OT labels to `x₀ ∧ x₁`, by computation.
example : ∀ a b : Fin 1 → Bool,
    let G := garbleWith andC Boolean.interpretation toyF id toyKey toyPerm
    yaoDecode (n₀ := 1) (n₁ := 1) toyF id (.ofGarbled G a)
      (fun j => G.encoding (Fin.natAdd 1 j) (b j)) = ![a 0 && b 0] := by
  decide

-- Correctness: in every run the evaluator outputs `x₀ ∧ x₁` and the garbler outputs nothing.
example (x : (i : Fin 2) → YaoIn 1 1 i)
    {r : ((i : Fin 2) → PartyView (YaoIn 1 1) (YaoCoins andC Bool) (yaoSchedule andC Bool) i) ×
      ((i : Fin 2) → YaoOut 1 i)}
    (hr : r ∈ ((yaoProtocol andC Boolean.interpretation toyF id).evalWith
      (batchOTWorld 1 (Bool × Bool)) x).support) :
    r.2 = yaoOutputs ![x 0 0 && x 1 0] := by
  rw [yao_output_of_mem_support andC Boolean.interpretation toyF id x hr]
  congr 1
  funext j
  fin_cases j
  rfl

-- A corrupted garbler has advantage zero.
example (x : (i : Fin 2) → YaoIn 1 1 i)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView (YaoIn 1 1) (YaoCoins andC Bool) (yaoSchedule andC Bool) i) ×
      ((i : Fin 2) → YaoOut 1 i) → ProbComp Bool) :
    semiHonestAdvantage (yaoProtocol andC Boolean.interpretation toyF id)
      (batchOTWorld 1 (Bool × Bool)) (yaoFunctionality andC Boolean.interpretation) {0}
      (yaoGarblerSim andC Bool) x D = 0 :=
  semiHonestAdvantage_yao_garbler andC Boolean.interpretation toyF id x D

-- A corrupted evaluator's advantage is at most the sum of three PRF advantages, one per wire.
-- This checks that `htw` is satisfiable (by `id`); with the toy `F` the right side is not small.
example (x : (i : Fin 2) → YaoIn 1 1 i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (YaoIn 1 1) (YaoCoins andC Bool) (yaoSchedule andC Bool) i) ×
      ((i : Fin 2) → YaoOut 1 i) → ProbComp Bool) :
    semiHonestAdvantage (yaoProtocol andC Boolean.interpretation toyF id)
        (batchOTWorld 1 (Bool × Bool)) (yaoFunctionality andC Boolean.interpretation) {1}
        (yaoEvaluatorSim andC toyF id) x D ≤
      ∑ j ∈ Finset.range 3, PRF.advantage toyF (reduction andC Boolean.interpretation toyF id
        (yaoInput x) (yaoEvaluatorDistinguisher andC (x 1)
          (andC.eval Boolean.interpretation (yaoInput x)) D) j) :=
  semiHonestAdvantage_yao_evaluator_le andC Boolean.interpretation toyF id Function.injective_id
    x D

end CslibFrontierTests.Crypto.Yao
