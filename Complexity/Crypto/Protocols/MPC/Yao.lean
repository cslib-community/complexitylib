/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.Privacy
public import Complexity.Crypto.Protocols.MPC.Advantage
public import Complexity.Crypto.Protocols.MPC.BatchOT

/-!
# Yao's two-party protocol in the oblivious-transfer hybrid model

Yao's protocol [Yao1986] for a Boolean circuit `C : Circuit σ (n₀ + n₁) m`, in the form analysed by
Lindell and Pinkas [LindellPinkas2009], with the point-and-permute garbling of
`Cslib.Crypto.Garbling`. Party `0`, the garbler, holds `x₀ : Fin n₀ → Bool`; party `1`, the
evaluator, holds `x₁ : Fin n₁ → Bool`. The garbler samples uniform wire keys and permutation bits,
garbles `C`, and sends the garbled table, the labels of its own input bits and the decoding bits.
The parties then make one call to the ideal batched oblivious transfer `batchOTSpec n₁ (K × Bool)`:
the garbler offers both labels of each of the evaluator's input wires and the evaluator chooses
with its input bits. The evaluator evaluates the table on all input labels and decodes. Only the
evaluator receives an output, `C.eval I (Fin.append x₀ x₁)` (`yaoFunctionality`).

* **Correctness** (`yao_output_of_mem_support`): in every run the evaluator outputs
  `C.eval I (Fin.append x₀ x₁)`, exactly, for every round function `F` and tweak map `tw`.
* **Privacy against the garbler** (`idealJoint_yao_garbler`): the garbler receives nothing but `()`
  from the oblivious transfer, so the simulator `yaoGarblerSim` that samples fresh coins makes the
  ideal and real joint distributions equal; every distinguisher has advantage zero.
* **Privacy against the evaluator** (`semiHonestAdvantage_yao_evaluator_le`): the simulator
  `yaoEvaluatorSim` places the garbling simulator's view, computed from the topology of `C` and the
  evaluator's output, into the evaluator's view. The advantage `semiHonestAdvantage` of a
  distinguisher `D` on the evaluator's view and the outputs is at most the sum over the
  `n₀ + n₁ + C.size` wires of the PRF advantage of the reductions of
  `Cslib.Crypto.Garbling.advantage_realGame_simGame_le`, run against the distinguisher on garbled
  views that `D` induces (`yaoEvaluatorDistinguisher`). The tweak map must be injective; the
  identity is.

These are the two cases of Goldreich's two-party semi-honest definition (Definition 7.2.1), one
simulator per corrupted party, stated on the joint distribution of the corrupted party's view and
both outputs, with a concrete distinguishing advantage in place of computational
indistinguishability.

Scope: the oblivious transfer is the ideal oracle, and no composition theorem replaces it by a
protocol. The bounds are for a single instance (circuit, inputs and distinguisher fixed), with no
security parameter; running time is not tracked, and neither the simulators nor the reductions are
certified efficient. Only the evaluator learns the output; the variant in which the garbler also
learns an output is not covered.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.yaoProtocol`: the protocol, with schedule `yaoSchedule`.
* `Cslib.Crypto.Protocols.MPC.yaoFunctionality`: the functionality it computes.
* `Cslib.Crypto.Protocols.MPC.yaoGarblerSim`, `Cslib.Crypto.Protocols.MPC.yaoEvaluatorSim`: the
  simulators.

## Main results

* `Cslib.Crypto.Protocols.MPC.yao_output_of_mem_support`: correctness.
* `Cslib.Crypto.Protocols.MPC.idealJoint_yao_garbler`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_yao_garbler`: perfect privacy against the garbler.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_yao_evaluator_le`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_yao_evaluator_le_mul`: privacy against the
  evaluator from the PRF security of the round function.

## References

* [A. C. Yao, *How to Generate and Exchange Secrets*][Yao1986]
* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.2.2.1 (Definition 7.2.1, pp. 620–622).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Circuits Cslib.Crypto.Garbling Probability
open scoped NNReal

universe v

variable {σ : Signature.{v}} {n₀ n₁ m : ℕ} {K T : Type}

/-- The inputs: `n₀` bits for the garbler (party `0`) and `n₁` bits for the evaluator
(party `1`). -/
@[expose, reducible] def YaoIn (n₀ n₁ : ℕ) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (Fin n₀ → Bool) (fun _ => Fin n₁ → Bool) i

/-- The garbler's coins: a key for each wire and colour, and a permutation bit for each wire. -/
@[expose, reducible] def GarblerCoins (C : Circuit σ (n₀ + n₁) m) (K : Type) : Type :=
  (Wire (n₀ + n₁) C.size × Bool → K) × (Wire (n₀ + n₁) C.size → Bool)

/-- The coins: the garbler's keys and permutation bits; the evaluator uses none. -/
@[expose, reducible] def YaoCoins (C : Circuit σ (n₀ + n₁) m) (K : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (GarblerCoins C K) (fun _ => Unit) i

/-- The outputs: nothing for the garbler and the circuit's output for the evaluator. -/
@[expose, reducible] def YaoOut (m : ℕ) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) Unit (fun _ => Fin m → Bool) i

/-- The garbler's message: the garbled table, the labels of its own input bits and the decoding
bits. -/
@[ext] structure YaoMessage (n₀ : ℕ) {n₁ m s : ℕ} (τ : Circuit.Topology (n₀ + n₁) m s)
    (K : Type) where
  /-- The garbled table. -/
  table : Row τ → K × Bool
  /-- The labels of the garbler's input bits. -/
  labels : Fin n₀ → K × Bool
  /-- The decoding bits. -/
  decoding : Fin m → Bool

/-- The schedule: the garbler sends its message, then the parties run one batched oblivious
transfer of the labels of the evaluator's input bits. -/
@[expose, reducible] def yaoSchedule (C : Circuit σ (n₀ + n₁) m) (K : Type) :
    Schedule 2 (batchOTSpec n₁ (K × Bool)) :=
  [.message 0 1 (YaoMessage n₀ C.topology K),
    .oracle () (Function.Embedding.refl (Fin 2))]

/-- The garbler's message for a garbled circuit and the garbler's input. -/
@[expose] def YaoMessage.ofGarbled {s : ℕ} {τ : Circuit.Topology (n₀ + n₁) m s}
    (G : Garbled τ K) (x₀ : Fin n₀ → Bool) : YaoMessage n₀ τ K where
  table := G.table
  labels := fun i => G.encoding (Fin.castAdd n₁ i) (x₀ i)
  decoding := G.decoding

/-- The evaluator's output: evaluate the table on the garbler's labels followed by its own, then
decode. -/
@[expose] def yaoDecode {s : ℕ} {τ : Circuit.Topology (n₀ + n₁) m s} [AddCommGroup K]
    (F : K → T → K × Bool) (tw : Slot τ → T) (M : YaoMessage n₀ τ K)
    (Y : Fin n₁ → K × Bool) : Fin m → Bool :=
  decode M.decoding (evaluate τ F tw M.table (Fin.append M.labels Y))

/-- The local state of each party after the oblivious transfer. -/
@[expose, reducible] def YaoFinal (C : Circuit σ (n₀ + n₁) m) (K : Type) (i : Fin 2) : Type :=
  ((YaoIn n₀ n₁ i × YaoCoins C K i) ×
      (Round.message (spec := batchOTSpec n₁ (K × Bool)) 0 1
        (YaoMessage n₀ C.topology K)).Received i) ×
    (Round.oracle (spec := batchOTSpec n₁ (K × Bool)) ()
      (Function.Embedding.refl (Fin 2))).Received i

/-- Sample the garbler's coins uniformly. -/
@[expose] noncomputable def sampleGarblerCoins (C : Circuit σ (n₀ + n₁) m) (K : Type)
    [Fintype K] [Nonempty K] :
    ProbComp (GarblerCoins C K) := do
  let key ← ProbComp.uniform (Wire (n₀ + n₁) C.size × Bool → K)
  let perm ← ProbComp.uniform (Wire (n₀ + n₁) C.size → Bool)
  return (key, perm)

/-- The garbler's coins as a coin tuple. -/
@[expose] def yaoCoins (C : Circuit σ (n₀ + n₁) m) (c : GarblerCoins C K) :
    (i : Fin 2) → YaoCoins C K i :=
  fun i => Fin.cases (motive := fun i => YaoCoins C K i) c (fun _ => ()) i

/-- The circuit's input: the garbler's bits followed by the evaluator's. -/
@[expose] def yaoInput (x : (i : Fin 2) → YaoIn n₀ n₁ i) : Fin (n₀ + n₁) → Bool :=
  Fin.append (x 0) (x 1)

/-- The output tuple for a circuit output `y`: nothing for the garbler, `y` for the evaluator. -/
@[expose] def yaoOutputs (y : Fin m → Bool) : (i : Fin 2) → YaoOut m i :=
  fun i => Fin.cases (motive := fun i => YaoOut m i) () (fun _ => y) i

/-- The two-party functionality: the evaluator learns `C.eval I (Fin.append x₀ x₁)` and the
garbler learns nothing. -/
@[expose] def yaoFunctionality (C : Circuit σ (n₀ + n₁) m) (I : Interpretation σ Bool) :
    Functionality 2 (YaoIn n₀ n₁) (YaoOut m) :=
  .ofDeterministic fun x => yaoOutputs (C.eval I (yaoInput x))

/-- The evaluator's view when the view of the garbled circuit is `V` and its input is `x₁`:
the garbler's message carries the table, the labels of the garbler's input wires and the decoding
bits, and the oblivious transfer delivers the labels of the evaluator's input wires. -/
@[expose] def evaluatorView (C : Circuit σ (n₀ + n₁) m) (x₁ : Fin n₁ → Bool)
    (V : View C.topology K) : PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) 1 where
  input := x₁
  coins := ()
  received :=
    (fun _ => ⟨V.table, fun i => V.input (Fin.castAdd n₁ i), V.decoding⟩,
      (fun s _ => Fin.cases (motive := fun s => (batchOTSpec n₁ (K × Bool)).Answer () s) ()
        (fun _ j => V.input (Fin.natAdd n₀ j)) s, ()))

/-- The garbler's view: its input and coins; it receives nothing. -/
@[expose] def garblerView (C : Circuit σ (n₀ + n₁) m) (x₀ : Fin n₀ → Bool) (c : GarblerCoins C K) :
    PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) 0 where
  input := x₀
  coins := c
  received :=
    (fun h => absurd h (by decide),
      (fun s hs => Fin.cases (motive := fun s => s = 0 → (batchOTSpec n₁ (K × Bool)).Answer () s)
        (fun _ => ()) (fun j hj => absurd hj (Fin.succ_ne_zero j)) s hs, ()))

/-- The simulator for a corrupted garbler: fresh coins and nothing received. -/
@[expose] noncomputable def yaoGarblerSim (C : Circuit σ (n₀ + n₁) m) (K : Type) [Fintype K]
    [Nonempty K] :
    CoalitionSimulator (yaoSchedule C K) (YaoIn n₀ n₁) (YaoCoins C K) (YaoOut m) {0} :=
  fun xI _ => do
    let c ← sampleGarblerCoins C K
    return singletonView (garblerView C (xI ⟨0, Finset.mem_singleton_self 0⟩) c)

/-- The distinguisher on views of the garbled circuit that a distinguisher `D` on the evaluator's
joint view and outputs induces, for input tuple `x` and circuit output `y`. -/
@[expose] def yaoEvaluatorDistinguisher (C : Circuit σ (n₀ + n₁) m) (x₁ : Fin n₁ → Bool)
    (y : Fin m → Bool)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) i)
      × ((i : Fin 2) → YaoOut m i) → ProbComp Bool) (V : View C.topology K) : ProbComp Bool :=
  D (singletonView (evaluatorView C x₁ V), yaoOutputs y)

variable [AddCommGroup K]

/-- The garbler's message from its input and coins. -/
@[expose] def yaoSend (C : Circuit σ (n₀ + n₁) m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (st : (Fin n₀ → Bool) × GarblerCoins C K) : YaoMessage n₀ C.topology K :=
  .ofGarbled (garbleWith C I F tw st.2.1 st.2.2) st.1

/-- The oblivious-transfer queries: the garbler offers both labels of each of the evaluator's
input wires, and the evaluator chooses with its input bits. -/
@[expose] def yaoQuery (C : Circuit σ (n₀ + n₁) m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (s : Fin 2)
    (st : (YaoIn n₀ n₁ s × YaoCoins C K s) ×
      (Round.message (spec := batchOTSpec n₁ (K × Bool)) 0 1
        (YaoMessage n₀ C.topology K)).Received s) :
    (batchOTSpec n₁ (K × Bool)).Query () s :=
  Fin.cases
    (motive := fun s => (YaoIn n₀ n₁ s × YaoCoins C K s) ×
      (Round.message (spec := batchOTSpec n₁ (K × Bool)) 0 1
        (YaoMessage n₀ C.topology K)).Received s → (batchOTSpec n₁ (K × Bool)).Query () s)
    (fun st => fun j => (garbleWith C I F tw st.1.2.1 st.1.2.2).encoding (Fin.natAdd n₀ j))
    (fun _ st => st.1.1) s st

/-- The outputs: the garbler outputs nothing; the evaluator decodes with the garbler's message and
the labels from the oblivious transfer. -/
@[expose] def yaoOutput (C : Circuit σ (n₀ + n₁) m) (F : K → T → K × Bool)
    (tw : Slot C.topology → T) (i : Fin 2) (st : YaoFinal C K i) : YaoOut m i :=
  Fin.cases (motive := fun i => YaoFinal C K i → YaoOut m i)
    (fun _ => ())
    (fun j st => yaoDecode F tw (st.1.2 (Fin.fin_one_eq_zero j ▸ rfl))
      (st.2 1 (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- **Yao's protocol** in the batched oblivious-transfer hybrid model. The garbler garbles `C`
with uniform keys and permutation bits and sends the garbled table, the labels of its own input
bits and the decoding bits. The evaluator obtains the labels of its input bits by one batched
oblivious transfer, evaluates the table and decodes. -/
@[expose] noncomputable def yaoProtocol [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T) :
    Protocol 2 (batchOTSpec n₁ (K × Bool)) (yaoSchedule C K) (YaoIn n₀ n₁) (YaoCoins C K)
      (YaoOut m) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (YaoCoins C K i))
    (sampleGarblerCoins C K) (fun _ => pure ()) i
  steps := .message (yaoSend C I F tw) (.oracle (yaoQuery C I F tw) (.done (yaoOutput C F tw)))

/-- The transcripts received in a run from the local states `st` after coin sampling. -/
private def yaoReceived (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (st : (i : Fin 2) → YaoIn n₀ n₁ i × YaoCoins C K i) (i : Fin 2) :
    (yaoSchedule C K).Received i :=
  (Round.deliverMessage (yaoSend C I F tw (st 0)) i,
    Round.deliverOracle (spec := batchOTSpec n₁ (K × Bool)) (op := ())
      (Function.Embedding.refl (Fin 2))
      (batchOTAnswer fun s => yaoQuery C I F tw s (st s, Round.deliverMessage
        (yaoSend C I F tw (st 0)) s)) i, ())

/-- The protocol's steps are deterministic once the coins are fixed. -/
private theorem evalWith_yaoSteps [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (st : (i : Fin 2) → YaoIn n₀ n₁ i × YaoCoins C K i) :
    (yaoProtocol C I F tw).steps.evalWith (batchOTWorld n₁ (K × Bool)) st =
      PMF.pure (yaoReceived C I F tw st) := by
  refine (Steps.evalWith_message _ _ _ _).trans ?_
  refine (congrArg (PMF.map _) (Steps.evalWith_oracle _ _ _ _)).trans ?_
  simp only [Steps.evalWith_done, batchOTWorld, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
  rfl

/-- Independent coin sampling draws the garbler's coins. -/
private theorem eval_pi_yaoSampleCoins [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T) :
    ProbComp.eval (OracleComp.pi (yaoProtocol C I F tw).sampleCoins) =
      (ProbComp.eval (sampleGarblerCoins C K)).map (yaoCoins C) := by
  have h1 : ProbComp.eval ((yaoProtocol C I F tw).sampleCoins (Fin.succ 0)) =
      PMF.pure (show YaoCoins C K (Fin.succ 0) from ()) := rfl
  simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, h1]
  erw [PMF.pure_bind]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  refine congrArg (PMF.bind _) (funext fun c => congrArg PMF.pure (funext fun i => ?_))
  fin_cases i <;> rfl

/-- Decoding the message of a garbled circuit with the labels of the evaluator's bits runs the
garbled circuit on the whole input. -/
theorem yaoDecode_ofGarbled {s : ℕ} {τ : Circuit.Topology (n₀ + n₁) m s} (G : Garbled τ K)
    (F : K → T → K × Bool) (tw : Slot τ → T) (x₀ : Fin n₀ → Bool) (x₁ : Fin n₁ → Bool) :
    yaoDecode F tw (.ofGarbled G x₀) (fun j => G.encoding (Fin.natAdd n₀ j) (x₁ j)) =
      G.run F tw (Fin.append x₀ x₁) := by
  simp only [yaoDecode, Garbled.run, YaoMessage.ofGarbled]
  congr 2
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right, encode]

/-- In a run with the garbler's coins `c`, the evaluator outputs the circuit's output. -/
private theorem outputOfView_yao_one [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) (c : GarblerCoins C K) :
    (yaoProtocol C I F tw).outputOfView 1
        ⟨x 1, yaoCoins C c 1, yaoReceived C I F tw (fun i => (x i, yaoCoins C c i)) 1⟩ =
      C.eval I (yaoInput x) :=
  (yaoDecode_ofGarbled (garbleWith C I F tw c.1 c.2) F tw (x 0) (x 1)).trans
    (Garbled.run_garbleWith C I F tw c.1 c.2 _)

/-- The views and outputs of a run of Yao's protocol, from the garbler's coins. -/
private theorem evalWith_yao [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) :
    (yaoProtocol C I F tw).evalWith (batchOTWorld n₁ (K × Bool)) x =
      (ProbComp.eval (sampleGarblerCoins C K)).map fun c =>
        (fun i => ⟨x i, yaoCoins C c i, yaoReceived C I F tw (fun i => (x i, yaoCoins C c i)) i⟩,
          yaoOutputs (C.eval I (yaoInput x))) := by
  rw [Protocol.evalWith_eq, eval_pi_yaoSampleCoins]
  simp only [evalWith_yaoSteps, PMF.pure_map, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  refine congrArg _ (funext fun c => ?_)
  simp only [Function.comp_apply]
  refine congrArg PMF.pure (Prod.ext rfl ?_)
  funext i
  fin_cases i
  · rfl
  · exact outputOfView_yao_one C I F tw x c

/-- The randomized garbling is the deterministic garbling of uniform coins. -/
private theorem eval_garble [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T) :
    ProbComp.eval (garble C I F tw) =
      (ProbComp.eval (sampleGarblerCoins C K)).map fun c => garbleWith C I F tw c.1 c.2 := by
  simp only [garble, sampleGarblerCoins, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
    PMF.pure_map]

/-- The evaluator's view in a run with the garbler's coins `c`. -/
private theorem yaoReceived_one (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) (c : GarblerCoins C K) :
    (⟨x 1, yaoCoins C c 1, yaoReceived C I F tw (fun i => (x i, yaoCoins C c i)) 1⟩ :
        PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) 1) =
      evaluatorView C (x 1) ((garbleWith C I F tw c.1 c.2).view (yaoInput x)) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · refine Round.received_message_ext fun _ => YaoMessage.ext rfl ?_ rfl
    funext i
    change (garbleWith C I F tw c.1 c.2).encoding (Fin.castAdd n₁ i) (x 0 i) =
      (garbleWith C I F tw c.1 c.2).encoding (Fin.castAdd n₁ i) (yaoInput x (Fin.castAdd n₁ i))
    exact congrArg _ (Fin.append_left (x 0 : Fin n₀ → Bool) (x 1 : Fin n₁ → Bool) i).symm
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · simp at hs
    · funext j
      change (garbleWith C I F tw c.1 c.2).encoding (Fin.natAdd n₀ j) (x 1 j) =
        (garbleWith C I F tw c.1 c.2).encoding (Fin.natAdd n₀ j) (yaoInput x (Fin.natAdd n₀ j))
      exact congrArg _ (Fin.append_right (x 0 : Fin n₀ → Bool) (x 1 : Fin n₁ → Bool) j).symm

/-- The garbler's view in a run with its coins `c`. -/
private theorem yaoReceived_zero (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) (c : GarblerCoins C K) :
    (⟨x 0, yaoCoins C c 0, yaoReceived C I F tw (fun i => (x i, yaoCoins C c i)) 0⟩ :
        PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) 0) = garblerView C (x 0) c := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · rfl
    · simp at hs

/-- **Correctness**: in every run of Yao's protocol the evaluator outputs
`C.eval I (Fin.append x₀ x₁)` and the garbler outputs nothing. -/
theorem yao_output_of_mem_support [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i)
    {r : ((i : Fin 2) → PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) i) ×
      ((i : Fin 2) → YaoOut m i)}
    (hr : r ∈ ((yaoProtocol C I F tw).evalWith (batchOTWorld n₁ (K × Bool)) x).support) :
    r.2 = yaoOutputs (C.eval I (yaoInput x)) := by
  rw [evalWith_yao, PMF.mem_support_map_iff] at hr
  obtain ⟨c, -, rfl⟩ := hr
  rfl

/-- The real joint distribution for a corrupted evaluator: its view is determined by the view of
the garbled circuit on the whole input. -/
theorem realJoint_yao_evaluator [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) :
    (yaoProtocol C I F tw).realJoint (batchOTWorld n₁ (K × Bool)) {1} x =
      (ProbComp.eval (garble C I F tw)).map fun G =>
        (singletonView (evaluatorView C (x 1) (G.view (yaoInput x))),
          yaoOutputs (C.eval I (yaoInput x))) := by
  rw [Protocol.realJoint, evalWith_yao, eval_garble, PMF.map_comp, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun c => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [yaoReceived_one]

/-- The real joint distribution for a corrupted garbler: fresh coins and nothing received. -/
theorem realJoint_yao_garbler [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) :
    (yaoProtocol C I F tw).realJoint (batchOTWorld n₁ (K × Bool)) {0} x =
      (ProbComp.eval (sampleGarblerCoins C K)).map fun c =>
        (singletonView (garblerView C (x 0) c), yaoOutputs (C.eval I (yaoInput x))) := by
  rw [Protocol.realJoint, evalWith_yao, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun c => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [yaoReceived_zero]

/-- **Perfect privacy against the garbler**: the ideal joint distribution with the simulator
`yaoGarblerSim` equals the real one. -/
theorem idealJoint_yao_garbler [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i) :
    ProbComp.eval (idealJoint (yaoFunctionality C I) {0} (yaoGarblerSim C K) x) =
      (yaoProtocol C I F tw).realJoint (batchOTWorld n₁ (K × Bool)) {0} x := by
  rw [realJoint_yao_garbler]
  simp only [idealJoint, yaoFunctionality, Functionality.ofDeterministic, yaoGarblerSim,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_bind]
  rw [← PMF.bind_pure_comp]
  rfl

/-- A corrupted garbler has advantage zero against every distinguisher. -/
theorem semiHonestAdvantage_yao_garbler [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (x : (i : Fin 2) → YaoIn n₀ n₁ i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) i)
      × ((i : Fin 2) → YaoOut m i) → ProbComp Bool) :
    semiHonestAdvantage (yaoProtocol C I F tw) (batchOTWorld n₁ (K × Bool)) (yaoFunctionality C I)
      {0} (yaoGarblerSim C K) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mpr (idealJoint_yao_garbler C I F tw x) D

/-- The simulator for a corrupted evaluator: the simulated view of the garbled circuit from the
topology and the output, placed in the evaluator's view. -/
@[expose] noncomputable def yaoEvaluatorSim [Fintype K] [Nonempty K] (C : Circuit σ (n₀ + n₁) m)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) :
    CoalitionSimulator (yaoSchedule C K) (YaoIn n₀ n₁) (YaoCoins C K) (YaoOut m) {1} :=
  fun xI yI => do
    let V ← simulate C.topology F tw (yI ⟨1, Finset.mem_singleton_self 1⟩)
    return singletonView (evaluatorView C (xI ⟨1, Finset.mem_singleton_self 1⟩) V)

variable [Fintype K] [Nonempty K] [Fintype T] [DecidableEq T]

/-- **Privacy against the evaluator**: every distinguisher's advantage between the ideal joint
distribution with `yaoEvaluatorSim` and the real one is at most the sum of the PRF advantages of
the `n₀ + n₁ + C.size` reductions of the garbling scheme, against the distinguisher on views of the
garbled circuit that `D` induces. -/
theorem semiHonestAdvantage_yao_evaluator_le (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (htw : Function.Injective tw) (x : (i : Fin 2) → YaoIn n₀ n₁ i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) i)
      × ((i : Fin 2) → YaoOut m i) → ProbComp Bool) :
    semiHonestAdvantage (yaoProtocol C I F tw) (batchOTWorld n₁ (K × Bool)) (yaoFunctionality C I)
        {1} (yaoEvaluatorSim C F tw) x D ≤
      ∑ j ∈ Finset.range (n₀ + n₁ + C.size), PRF.advantage F (reduction C I F tw (yaoInput x)
        (yaoEvaluatorDistinguisher C (x 1) (C.eval I (yaoInput x)) D) j) := by
  have hideal : ProbComp.eval (idealJoint (yaoFunctionality C I) {1} (yaoEvaluatorSim C F tw) x >>=
      D) = simGame C I F tw (yaoInput x)
        (yaoEvaluatorDistinguisher C (x 1) (C.eval I (yaoInput x)) D) := by
    simp only [idealJoint, yaoFunctionality, Functionality.ofDeterministic, yaoEvaluatorSim,
      simGame, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_bind]
    rfl
  have hreal : ((yaoProtocol C I F tw).realJoint (batchOTWorld n₁ (K × Bool)) {1} x).bind
      (fun r => ProbComp.eval (D r)) = realGame C I F tw (yaoInput x)
        (yaoEvaluatorDistinguisher C (x 1) (C.eval I (yaoInput x)) D) := by
    rw [realJoint_yao_evaluator, PMF.bind_map, realGame, ProbComp.eval_bind]
    rfl
  rw [semiHonestAdvantage, hideal, hreal, Game.advantage_comm]
  exact advantage_realGame_simGame_le C I F tw htw _ _

/-- **Privacy against the evaluator** with a uniform bound `ε` on the PRF advantage of each
reduction: the advantage is at most `(n₀ + n₁ + C.size) * ε`. -/
theorem semiHonestAdvantage_yao_evaluator_le_mul (C : Circuit σ (n₀ + n₁) m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (htw : Function.Injective tw) (x : (i : Fin 2) → YaoIn n₀ n₁ i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (YaoIn n₀ n₁) (YaoCoins C K) (yaoSchedule C K) i)
      × ((i : Fin 2) → YaoOut m i) → ProbComp Bool) (ε : ℝ≥0)
    (hε : ∀ j < n₀ + n₁ + C.size, PRF.advantage F (reduction C I F tw (yaoInput x)
      (yaoEvaluatorDistinguisher C (x 1) (C.eval I (yaoInput x)) D) j) ≤ ε) :
    semiHonestAdvantage (yaoProtocol C I F tw) (batchOTWorld n₁ (K × Bool)) (yaoFunctionality C I)
        {1} (yaoEvaluatorSim C F tw) x D ≤ (n₀ + n₁ + C.size) * ε := by
  refine (semiHonestAdvantage_yao_evaluator_le C I F tw htw x D).trans ?_
  calc _ ≤ ∑ _j ∈ Finset.range (n₀ + n₁ + C.size), ε :=
        Finset.sum_le_sum fun j hj => hε j (Finset.mem_range.mp hj)
    _ = (n₀ + n₁ + C.size) * ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_add]

end Cslib.Crypto.Protocols.MPC
