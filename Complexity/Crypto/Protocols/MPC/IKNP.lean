/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.CorrelationRobust
public import Complexity.Crypto.Protocols.MPC.Advantage
public import Complexity.Crypto.Protocols.MPC.BatchOT

/-!
# IKNP oblivious-transfer extension

The protocol of Ishai, Kilian, Nissim and Petrank [IshaiKilianNissimPetrank2003, Section 3,
Figure 1], which implements `m` transfers of values in `L` from `κ` base transfers of `m`-bit
strings and a correlation-robust family `H : Fin m → BitString κ → L`
(`Cslib.Crypto.CorrelationRobust`). Party `0`, the sender, holds pairs `X : Fin m → Bool → L`;
party `1`, the receiver, holds choice bits `r : Fin m → Bool`. The functionality is the ideal
batched transfer `batchOTFunctionality m L`, which gives `fun j => X j (r j)` to the receiver and
nothing to the sender.

1. The receiver samples a uniform `m × κ` matrix `T`, with rows `tⱼ` and columns `tⁱ`. The parties
   make one call to `batchOTSpec κ (BitString m)` with the roles reversed (`iknpRoleReversal`): the
   receiver offers the pair `(tⁱ, tⁱ + r)` for each `i`, and the sender chooses with a uniform
   `s : BitString κ`. The sender learns the matrix with rows `qⱼ = tⱼ + rⱼ s`.
2. The sender sends `X j b + H j (qⱼ + b s)` for each `j` and `b` (`iknpMasked`).
3. The receiver outputs `Y j (r j) - H j tⱼ`; its mask is `H j tⱼ` because `qⱼ + rⱼ s = tⱼ`
   (`iknp_mask_input`).

The paper's values are bit strings, `L = BitString ℓ`, where subtraction is addition; here `L` is
any finite additive commutative group.

* **Correctness** (`iknp_output_of_mem_support`): in every run the receiver outputs
  `fun j => X j (r j)`, for every `H`.
* **Privacy against the sender** (`idealJoint_iknp_sender`): the columns `tⁱ + sᵢ r` that the
  sender receives are uniform whatever `s` and `r` are, so the simulator `iknpSenderSim`, which
  samples them afresh, makes the ideal and real joint distributions equal.
* **Privacy against the receiver** (`semiHonestAdvantage_iknp_receiver`): the entries the receiver
  did not choose are masked by `H j (tⱼ + s)`, with `s` uniform and hidden from it, and the
  receiver knows `tⱼ`. That is the correlation-robustness experiment, so the advantage of every
  distinguisher `D` against the simulator `iknpReceiverSim` *equals* the correlation-robustness
  advantage of the explicit reduction `iknpReduction H x D`.

These are the two cases of Goldreich's two-party semi-honest definition (Definition 7.2.1), one
simulator per corrupted party, stated on the joint distribution of the corrupted party's view and
both outputs, with a concrete advantage in place of computational indistinguishability.

Scope: the base transfers are the ideal oracle, and no composition theorem replaces them by a
protocol. The statements are for a single instance (`H`, inputs and distinguisher fixed), with no
security parameter; running time is not tracked, and neither the simulators nor the reduction are
certified efficient. Only semi-honest security is covered, not the malicious variant of the
paper.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.iknpProtocol`: the protocol, with schedule `iknpSchedule`.
* `Cslib.Crypto.Protocols.MPC.iknpSenderSim`, `Cslib.Crypto.Protocols.MPC.iknpReceiverSim`: the
  simulators.
* `Cslib.Crypto.Protocols.MPC.iknpReduction`: the reduction to correlation robustness.

## Main results

* `Cslib.Crypto.Protocols.MPC.iknp_output_of_mem_support`: correctness.
* `Cslib.Crypto.Protocols.MPC.idealJoint_iknp_sender`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_iknp_sender`: perfect privacy against the
  sender.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_iknp_receiver`: privacy against the receiver
  from the correlation robustness of `H`.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003], Section 3.
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.2.2.1 (Definition 7.2.1, pp. 620–622).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Crypto Probability
open scoped NNReal

variable {κ m : ℕ} {L : Type}

/-- The coins: the sender's base choice string `s` and the receiver's matrix `T`, by rows. -/
@[expose, reducible] def IKNPCoins (κ m : ℕ) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (BitString κ) (fun _ => Fin m → BitString κ) i

/-- The parties of the base transfers, with the roles reversed: the extension's receiver
(party `1`) is the base sender (slot `0`), and the extension's sender (party `0`) is the base
receiver (slot `1`). -/
@[expose, reducible] def iknpRoleReversal : Fin 2 ↪ Fin 2 := ⟨Fin.rev, Fin.rev_injective⟩

/-- The schedule: `κ` base transfers of `m`-bit strings with the roles reversed, then the
sender's message of masked pairs. -/
@[expose, reducible] def iknpSchedule (κ m : ℕ) (L : Type) :
    Schedule 2 (batchOTSpec κ (BitString m)) :=
  [.oracle () iknpRoleReversal, .message 0 1 (Fin m → Bool → L)]

/-- The receiver's base-transfer input: for each column index `i` of `T`, the pair of `m`-bit
columns `(tⁱ, tⁱ + r)`. -/
@[expose] def iknpColumns (r : Fin m → Bool) (T : Fin m → BitString κ) :
    Fin κ → Bool → BitString m :=
  fun i b j => T j i + (b && r j)

/-- The rows of the matrix whose columns are `Q` (the transpose, `Function.swap Q`). -/
@[expose] def iknpRows (Q : Fin κ → BitString m) : Fin m → BitString κ :=
  fun j i => Q i j

/-- The sender's message: the pair `X j` masked by `H j qⱼ` and `H j (qⱼ + s)`, where `qⱼ` is
the `j`-th row of the matrix received from the base transfers. -/
@[expose] def iknpMasked [Add L] (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (s : BitString κ) (Q : Fin κ → BitString m) : Fin m → Bool → L :=
  fun j b => X j b + H j (if b then iknpRows Q j + s else iknpRows Q j)

/-- The base-transfer queries: the receiver offers the columns `(tⁱ, tⁱ + r)` and the sender
chooses with `s`. -/
@[expose] def iknpQuery (sl : Fin 2)
    (st : (batchOTSpec m L).Query () (iknpRoleReversal sl) × IKNPCoins κ m (iknpRoleReversal sl)) :
    (batchOTSpec κ (BitString m)).Query () sl :=
  Fin.cases
    (motive := fun sl => (batchOTSpec m L).Query () (iknpRoleReversal sl) ×
      IKNPCoins κ m (iknpRoleReversal sl) → (batchOTSpec κ (BitString m)).Query () sl)
    (fun st => iknpColumns st.1 st.2)
    (fun j => Fin.cases
      (motive := fun j => (batchOTSpec m L).Query () (iknpRoleReversal j.succ) ×
        IKNPCoins κ m (iknpRoleReversal j.succ) → (batchOTSpec κ (BitString m)).Query () j.succ)
      (fun st => st.2) (fun k => k.elim0) j)
    sl st

/-- The sender's message from its input, its coins and the columns it received. -/
@[expose] def iknpSend [Add L] (H : Fin m → BitString κ → L)
    (st : ((batchOTSpec m L).Query () 0 × IKNPCoins κ m 0) ×
      (Round.oracle (spec := batchOTSpec κ (BitString m)) () iknpRoleReversal).Received 0) :
    Fin m → Bool → L :=
  iknpMasked H st.1.1 st.1.2 (st.2 1 rfl)

/-- The local state of each party at the end of the protocol. -/
@[expose, reducible] def IKNPFinal (κ m : ℕ) (L : Type) (i : Fin 2) : Type :=
  (((batchOTSpec m L).Query () i × IKNPCoins κ m i) ×
      (Round.oracle (spec := batchOTSpec κ (BitString m)) () iknpRoleReversal).Received i) ×
    (Round.message (spec := batchOTSpec κ (BitString m)) 0 1 (Fin m → Bool → L)).Received i

/-- The outputs: the sender outputs nothing; the receiver unmasks the chosen entry of each pair
with `H j tⱼ`. -/
@[expose] def iknpOutput [AddGroup L] (H : Fin m → BitString κ → L) (i : Fin 2)
    (st : IKNPFinal κ m L i) : (batchOTSpec m L).Answer () i :=
  Fin.cases (motive := fun i => IKNPFinal κ m L i → (batchOTSpec m L).Answer () i)
    (fun _ => ())
    (fun j st k => st.2 (Fin.fin_one_eq_zero j ▸ rfl) k (st.1.1.1 k) - H k (st.1.1.2 k))
    i st

variable [AddCommGroup L]

/-- **The IKNP protocol** in the hybrid model with `κ` base transfers of `m`-bit strings. -/
@[expose] noncomputable def iknpProtocol (H : Fin m → BitString κ → L) :
    Protocol 2 (batchOTSpec κ (BitString m)) (iknpSchedule κ m L) ((batchOTSpec m L).Query ())
      (IKNPCoins κ m) ((batchOTSpec m L).Answer ()) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (IKNPCoins κ m i))
    (ProbComp.uniform (BitString κ)) (fun _ => ProbComp.uniform (Fin m → BitString κ)) i
  steps := .oracle iknpQuery (.message (iknpSend H) (.done (iknpOutput H)))

/-! ### Runs of the protocol -/

/-- Sample the coins: a uniform base choice string `s` and a uniform matrix `T`. -/
@[expose] noncomputable def sampleIKNPCoins (κ m : ℕ) :
    ProbComp (BitString κ × (Fin m → BitString κ)) := do
  let s ← ProbComp.uniform (BitString κ)
  let T ← ProbComp.uniform (Fin m → BitString κ)
  return (s, T)

/-- The coins `(s, T)` as a coin tuple. -/
@[expose] def iknpCoins (c : BitString κ × (Fin m → BitString κ)) : (i : Fin 2) → IKNPCoins κ m i :=
  fun i => Fin.cases (motive := fun i => IKNPCoins κ m i) c.1 (fun _ => c.2) i

/-- The sender's view: its input `X`, its base choice string `s` and the columns `Q` it receives
from the base transfers. -/
@[expose] def iknpSenderView (X : Fin m → Bool → L) (s : BitString κ) (Q : Fin κ → BitString m) :
    PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) 0 where
  input := X
  coins := s
  received :=
    (fun sl hsl => Fin.cases
      (motive := fun sl => iknpRoleReversal sl = 0 → (batchOTSpec κ (BitString m)).Answer () sl)
      (fun h => absurd h (by decide)) (fun _ _ => Q) sl hsl,
      fun h => absurd h (by simp), ())

/-- The receiver's view: its choice bits `r`, its matrix `T` and the masked pairs `Y`. -/
@[expose] def iknpReceiverView (r : Fin m → Bool) (T : Fin m → BitString κ)
    (Y : Fin m → Bool → L) :
    PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) 1 where
  input := r
  coins := T
  received :=
    (fun sl hsl => Fin.cases
      (motive := fun sl => iknpRoleReversal sl = 1 → (batchOTSpec κ (BitString m)).Answer () sl)
      (fun _ => ()) (fun j hj => absurd hj (by obtain rfl := Fin.fin_one_eq_zero j; decide))
      sl hsl,
      fun _ => Y, ())

/-- **The key identity**: the `j`-th row of the matrix the sender receives is `tⱼ` shifted by
`s` exactly when `rⱼ` holds, so the sender's two masks are `H j tⱼ` on the receiver's choice and
`H j (tⱼ + s)` on the other entry. -/
theorem iknp_mask_input (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ)
    (j : Fin m) (b : Bool) :
    (if b then iknpRows (fun i => iknpColumns r T i (s i)) j + s
      else iknpRows (fun i => iknpColumns r T i (s i)) j) =
      if b = r j then T j else T j + s := by
  funext i
  cases b <;> cases hr : r j <;>
    simp only [iknpRows, iknpColumns, hr, ↓reduceIte, Pi.add_apply, Bool.and_true,
      Bool.and_false, Bool.false_eq_true, Bool.true_eq_false] <;>
    cases T j i <;> cases s i <;> decide

/-- For fixed `s` and `r`, the map from the receiver's matrix to the columns the sender receives
is a bijection; so these columns are uniform when the matrix is. -/
private def iknpColumnsEquiv (r : Fin m → Bool) (s : BitString κ) :
    (Fin m → BitString κ) ≃ (Fin κ → BitString m) where
  toFun T i := iknpColumns r T i (s i)
  invFun Q j i := Q i j + (s i && r j)
  left_inv T := by
    funext j i
    simp only [iknpColumns]
    cases T j i <;> cases s i <;> cases r j <;> decide
  right_inv Q := by
    funext i j
    simp only [iknpColumns]
    cases Q i j <;> cases s i <;> cases r j <;> decide

/-- The transcripts received in a run from the local states `st` after coin sampling. -/
private def iknpReceived (H : Fin m → BitString κ → L)
    (st : (i : Fin 2) → (batchOTSpec m L).Query () i × IKNPCoins κ m i) (i : Fin 2) :
    (iknpSchedule κ m L).Received i :=
  (Round.deliverOracle (spec := batchOTSpec κ (BitString m)) iknpRoleReversal
      (batchOTAnswer fun sl => iknpQuery sl (st (iknpRoleReversal sl))) i,
    Round.deliverMessage (iknpSend H (st 0,
      Round.deliverOracle (spec := batchOTSpec κ (BitString m)) iknpRoleReversal
        (batchOTAnswer fun sl => iknpQuery sl (st (iknpRoleReversal sl))) 0)) i, ())

/-- The protocol's steps are deterministic once the coins are fixed. -/
private theorem evalWith_iknpSteps (H : Fin m → BitString κ → L)
    (st : (i : Fin 2) → (batchOTSpec m L).Query () i × IKNPCoins κ m i) :
    (iknpProtocol H).steps.evalWith (batchOTWorld κ (BitString m)) st =
      PMF.pure (iknpReceived H st) := by
  refine (Steps.evalWith_oracle _ _ _ _).trans ?_
  simp only [batchOTWorld, ProbComp.eval_pure, PMF.pure_bind, Steps.evalWith_message,
    Steps.evalWith_done, PMF.pure_map]
  rfl

/-- Independent coin sampling draws `(s, T)`. -/
private theorem eval_pi_iknpSampleCoins (H : Fin m → BitString κ → L) :
    ProbComp.eval (OracleComp.pi (iknpProtocol H).sampleCoins) =
      (ProbComp.eval (sampleIKNPCoins κ m)).map iknpCoins := by
  simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, sampleIKNPCoins, PMF.map_bind, PMF.pure_map]
  refine congrArg _ (funext fun s => ?_)
  exact congrArg (PMF.bind (ProbComp.eval (ProbComp.uniform (Fin m → BitString κ))))
    (funext fun T => congrArg PMF.pure (funext fun i => by fin_cases i <;> rfl))

/-- The receiver unmasks its chosen entry. -/
private theorem iknpMasked_sub (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ) (k : Fin m) :
    iknpMasked H X s (fun i => iknpColumns r T i (s i)) k (r k) - H k (T k) = X k (r k) := by
  simp only [iknpMasked]
  rw [iknp_mask_input, ite_eq_left_iff.mpr (absurd rfl), add_sub_cancel_right]

/-- In a run with coins `c`, the receiver outputs its chosen values. -/
private theorem outputOfView_iknp_one (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) (c : BitString κ × (Fin m → BitString κ)) :
    (iknpProtocol H).outputOfView 1
        ⟨x 1, iknpCoins c 1, iknpReceived H (fun i => (x i, iknpCoins c i)) 1⟩ =
      batchOTAnswer x 1 := by
  funext k
  change iknpMasked H (x 0) c.1 (fun i => iknpColumns (x 1) c.2 i (c.1 i)) k (x 1 k) -
    H k (c.2 k) = x 0 k (x 1 k)
  exact iknpMasked_sub H (x 0) (x 1) c.2 c.1 k

/-- The views and outputs of a run of the protocol, from the coins. -/
private theorem evalWith_iknp (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) :
    (iknpProtocol H).evalWith (batchOTWorld κ (BitString m)) x =
      (ProbComp.eval (sampleIKNPCoins κ m)).map fun c =>
        (fun i => ⟨x i, iknpCoins c i, iknpReceived H (fun i => (x i, iknpCoins c i)) i⟩,
          batchOTAnswer x) := by
  rw [Protocol.evalWith_eq, eval_pi_iknpSampleCoins]
  simp only [evalWith_iknpSteps, PMF.pure_map, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  refine congrArg _ (funext fun c => ?_)
  simp only [Function.comp_apply]
  refine congrArg PMF.pure (Prod.ext rfl ?_)
  funext i
  fin_cases i
  · rfl
  · exact outputOfView_iknp_one H x c

/-- **Correctness**: in every run the receiver outputs `fun j => X j (r j)` and the sender
outputs nothing. -/
theorem iknp_output_of_mem_support (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i)
    {res : ((i : Fin 2) → PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m)
        (iknpSchedule κ m L) i) × ((i : Fin 2) → (batchOTSpec m L).Answer () i)}
    (hres : res ∈ ((iknpProtocol H).evalWith (batchOTWorld κ (BitString m)) x).support) :
    res.2 = batchOTAnswer x := by
  rw [evalWith_iknp, PMF.mem_support_map_iff] at hres
  obtain ⟨c, -, rfl⟩ := hres
  rfl

/-! ### Privacy against the sender -/

/-- The simulator for a corrupted sender: a fresh base choice string and uniform columns. -/
@[expose] noncomputable def iknpSenderSim (κ m : ℕ) (L : Type) :
    CoalitionSimulator (iknpSchedule κ m L) ((batchOTSpec m L).Query ()) (IKNPCoins κ m)
      ((batchOTSpec m L).Answer ()) {0} :=
  fun xI _ => do
    let s ← ProbComp.uniform (BitString κ)
    let Q ← ProbComp.uniform (Fin κ → BitString m)
    return singletonView (iknpSenderView (xI ⟨0, Finset.mem_singleton_self 0⟩) s Q)

/-- The sender's view in a run with coins `c`. -/
private theorem iknpReceived_zero (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) (c : BitString κ × (Fin m → BitString κ)) :
    (⟨x 0, iknpCoins c 0, iknpReceived H (fun i => (x i, iknpCoins c i)) 0⟩ :
        PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) 0) =
      iknpSenderView (x 0) c.1 (fun i => iknpColumns (x 1) c.2 i (c.1 i)) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · refine Round.received_oracle_ext fun sl hsl => ?_
    fin_cases sl
    · exact absurd hsl (by simp [iknpRoleReversal])
    · rfl
  · exact Round.received_message_eq_of_ne (by simp) _ _

/-- The real joint distribution for a corrupted sender: its choice string and the columns it
receives, with `T` uniform. -/
theorem realJoint_iknp_sender (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) :
    (iknpProtocol H).realJoint (batchOTWorld κ (BitString m)) {0} x =
      (ProbComp.eval (sampleIKNPCoins κ m)).map fun c =>
        (singletonView (iknpSenderView (x 0) c.1 (fun i => iknpColumns (x 1) c.2 i (c.1 i))),
          batchOTAnswer x) := by
  rw [Protocol.realJoint, evalWith_iknp, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun c => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [iknpReceived_zero]

/-- **Perfect privacy against the sender**: the ideal joint distribution with `iknpSenderSim`
equals the real one, because the columns `tⁱ + sᵢ r` are uniform whatever `s` and `r` are. -/
theorem idealJoint_iknp_sender (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) :
    ProbComp.eval (idealJoint (batchOTFunctionality m L) {0} (iknpSenderSim κ m L) x) =
      (iknpProtocol H).realJoint (batchOTWorld κ (BitString m)) {0} x := by
  rw [realJoint_iknp_sender]
  simp only [idealJoint, batchOTFunctionality, Functionality.ofDeterministic, iknpSenderSim,
    sampleIKNPCoins, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind,
    PMF.bind_bind, PMF.map_bind, PMF.pure_map]
  refine congrArg _ (funext fun s => ?_)
  rw [← PMF.uniformOfFintype_map_equiv (iknpColumnsEquiv (x 1) s), PMF.bind_map]
  rfl

/-- A corrupted sender has advantage zero against every distinguisher. -/
theorem semiHonestAdvantage_iknp_sender (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) i) ×
      ((i : Fin 2) → (batchOTSpec m L).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage (iknpProtocol H) (batchOTWorld κ (BitString m))
      (batchOTFunctionality m L) {0} (iknpSenderSim κ m L) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mpr (idealJoint_iknp_sender H x) D

/-! ### Privacy against the receiver -/

/-- The simulator for a corrupted receiver with choice bits `r` and output `z`: a uniform matrix
`T`, the chosen entries `z j + H j tⱼ`, and uniform values in place of the other entries. -/
@[expose] noncomputable def iknpReceiverSim [Fintype L] (H : Fin m → BitString κ → L) :
    CoalitionSimulator (iknpSchedule κ m L) ((batchOTSpec m L).Query ()) (IKNPCoins κ m)
      ((batchOTSpec m L).Answer ()) {1} :=
  fun xI yI => do
    let T ← ProbComp.uniform (Fin m → BitString κ)
    let u ← ProbComp.uniform (Fin m → L)
    let r : Fin m → Bool := xI ⟨1, Finset.mem_singleton_self 1⟩
    let z : Fin m → L := yI ⟨1, Finset.mem_singleton_self 1⟩
    return singletonView (iknpReceiverView r T fun j b => if b = r j then z j + H j (T j) else u j)

/-- The correlation-robustness distinguisher that a distinguisher `D` on the receiver's joint
view and outputs induces, for the inputs `x`: given inputs `t` and values `w`, it masks the
chosen entries with `H j tⱼ` and the other entries with `w j`, and runs `D`. -/
@[expose] def iknpReduction (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) i) ×
      ((i : Fin 2) → (batchOTSpec m L).Answer () i) → ProbComp Bool) :
    CorrelationRobust.Adversary m (BitString κ) L :=
  fun p => D (singletonView (iknpReceiverView (x 1) p.1
      fun j b => x 0 j b + if b = x 1 j then H j (p.1 j) else p.2 j),
    batchOTAnswer x)

/-- The sender's message, by the key identity: the chosen entries are masked with `H j tⱼ` and
the others with `H j (tⱼ + s)`. -/
private theorem iknpMasked_eq (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ) :
    iknpMasked H X s (fun i => iknpColumns r T i (s i)) =
      fun j b => X j b + if b = r j then H j (T j) else H j (T j + s) := by
  funext j b
  simp only [iknpMasked]
  rw [iknp_mask_input, apply_ite (H j)]

/-- The simulated pairs with fresh values shifted by the unchosen entries are the pairs of the
reduction. -/
private theorem iknp_simulated_pairs (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (w : Fin m → L) :
    (fun j b => if b = r j then X j (r j) + H j (T j) else ((fun j => X j (!r j)) + w) j) =
      fun j b => X j b + if b = r j then H j (T j) else w j := by
  funext j b
  by_cases hb : b = r j
  · subst hb
    simp
  · obtain rfl : b = !r j := by cases b <;> cases h : r j <;> simp_all
    simp

/-- The receiver's view in a run with coins `c`: the entries it did not choose are masked with
`H j (tⱼ + s)`. -/
private theorem iknpReceived_one (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) (c : BitString κ × (Fin m → BitString κ)) :
    (⟨x 1, iknpCoins c 1, iknpReceived H (fun i => (x i, iknpCoins c i)) 1⟩ :
        PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) 1) =
      iknpReceiverView (x 1) c.2
        (fun j b => x 0 j b + if b = x 1 j then H j (c.2 j) else H j (c.2 j + c.1)) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · refine Round.received_oracle_ext fun sl hsl => ?_
    fin_cases sl
    · rfl
    · exact absurd hsl (by simp [iknpRoleReversal])
  · exact Round.received_message_ext fun _ => iknpMasked_eq H (x 0) (x 1) c.2 c.1

/-- The real joint distribution for a corrupted receiver. -/
theorem realJoint_iknp_receiver (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i) :
    (iknpProtocol H).realJoint (batchOTWorld κ (BitString m)) {1} x =
      (ProbComp.eval (sampleIKNPCoins κ m)).map fun c =>
        (singletonView (iknpReceiverView (x 1) c.2
          fun j b => x 0 j b + if b = x 1 j then H j (c.2 j) else H j (c.2 j + c.1)),
          batchOTAnswer x) := by
  rw [Protocol.realJoint, evalWith_iknp, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun c => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [iknpReceived_one]

/-- **Privacy against the receiver** (the security theorem of [IshaiKilianNissimPetrank2003] for
a corrupted receiver): every distinguisher's advantage between the ideal joint distribution with
`iknpReceiverSim` and the real one equals the correlation-robustness advantage of the reduction
`iknpReduction` against `H`. -/
theorem semiHonestAdvantage_iknp_receiver [Fintype L] (H : Fin m → BitString κ → L)
    (x : (i : Fin 2) → (batchOTSpec m L).Query () i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) i) ×
      ((i : Fin 2) → (batchOTSpec m L).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage (iknpProtocol H) (batchOTWorld κ (BitString m))
        (batchOTFunctionality m L) {1} (iknpReceiverSim H) x D =
      CorrelationRobust.advantage H (iknpReduction H x D) := by
  have hreal : ((iknpProtocol H).realJoint (batchOTWorld κ (BitString m)) {1} x).bind
      (fun res => ProbComp.eval (D res)) =
        CorrelationRobust.realGame H (iknpReduction H x D) := by
    rw [realJoint_iknp_receiver, PMF.bind_map]
    simp only [CorrelationRobust.realGame, sampleIKNPCoins, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    rfl
  have hideal : ProbComp.eval (idealJoint (batchOTFunctionality m L) {1} (iknpReceiverSim H) x >>=
      D) = CorrelationRobust.idealGame (iknpReduction H x D) := by
    simp only [CorrelationRobust.idealGame, idealJoint, batchOTFunctionality,
      Functionality.ofDeterministic, iknpReceiverSim, iknpReduction, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, PMF.bind_bind]
    refine congrArg _ (funext fun T => ?_)
    conv_lhs => rw [← PMF.uniformOfFintype_map_equiv
      (Equiv.addLeft (fun j => x 0 j (!x 1 j) : Fin m → L))]
    rw [PMF.bind_map]
    refine congrArg _ (funext fun w => ?_)
    exact congrArg (fun Y => ProbComp.eval (D (singletonView (iknpReceiverView (x 1) T Y),
      batchOTAnswer x))) (iknp_simulated_pairs H (x 0) (x 1) T w)
  rw [semiHonestAdvantage, hideal, hreal, Game.advantage_comm]

end Cslib.Crypto.Protocols.MPC
