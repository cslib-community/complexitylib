/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec

/-!
# Requests to a finite quantum device

An existing word-oracle program controls a fixed quantum register through three channels:
elementary gates, coherent oracle queries and single-wire measurements. Classical service
channels are disjoint. `DeviceRequest.codec` uses the existing phase-code encoding and unary wire
indices. It accepts exactly their canonical encodings. Malformed words receive the existing
`OracleCodec` rejection answer `[]`, with no state change. Encoded gates with invalid placements
are separately rejected by the device's existing gate decoder.

This is an interface for the existing native oracle machine, not a new program language or
efficiency predicate. The partial inverse specifies decoding mathematically; no efficiency of
a quantum-state simulation or of this partial inverse is asserted.

## Main definitions

* `Cslib.Quantum.DeviceOperation`: the three elementary quantum operation channels.
* `Cslib.Quantum.DeviceRequest`: typed requests with classical service channels.
* `Cslib.Quantum.DeviceRequest.codec`: their canonical word interface.
* `Cslib.Quantum.DeviceRequest.operationCost`: separate costs for each quantum operation.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- Quantum channels of a native controller. Classical service channels use the other summand. -/
inductive DeviceOperation where
  /-- Apply one elementary gate. -/
  | gate
  /-- Apply one coherent query to the fixed oracle. -/
  | query
  /-- Measure one active wire in the computational basis. -/
  | measure
  deriving DecidableEq

instance : Fintype DeviceOperation where
  elems := {.gate, .query, .measure}
  complete tag := by cases tag <;> simp

/-- Typed requests on a fixed `m`-qubit device, alongside classical service requests. -/
inductive DeviceRequest (m : ℕ) (Operation : Type) where
  /-- The existing elementary gate code, checked by its usual decoder. -/
  | gate (code : PhaseGateCode)
  /-- The coherent XOR query on the device's fixed argument and response registers. -/
  | query
  /-- Read one existing active wire. -/
  | measure (wire : Fin m)
  /-- Send a classical word to the service. -/
  | service (operation : Operation) (word : List Bool)
  deriving DecidableEq

namespace DeviceRequest

variable {m : ℕ} {Operation : Type}

/-- Gate payloads use `encPhaseGateCode`; query payloads are empty; measurement wires are unary.
Service payloads retain their original word and channel. -/
@[expose] def encode : DeviceRequest m Operation → (DeviceOperation ⊕ Operation) × List Bool
  | .gate code => (.inl .gate, encPhaseGateCode code)
  | .query => (.inl .query, [])
  | .measure wire => (.inl .measure, encUnary wire.val)
  | .service operation word => (.inr operation, word)

/-- The request encoding is injective, including its operation tag. -/
theorem encode_injective : Function.Injective (encode (m := m) (Operation := Operation)) := by
  intro q q' h
  cases q <;> cases q' <;> simp only [encode, Prod.mk.injEq, Sum.inl.injEq,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, reduceCtorEq,
    false_and, true_and] at h
  · exact congrArg DeviceRequest.gate (encPhaseGateCode.injective h)
  · rfl
  · exact congrArg DeviceRequest.measure (Fin.ext (encUnary.injective h))
  · obtain ⟨rfl, rfl⟩ := h
    rfl

/-- The canonical typed view of the native word channels. Replies are words already: gates and
queries return `[]`, measurements return one bit, and the service supplies a fixed-width word. -/
noncomputable def codec (m : ℕ) (Operation : Type) :
    OracleCodec (DeviceOperation ⊕ Operation) (DeviceRequest m Operation) (fun _ => List Bool) where
  encodeQuery := encode
  decodeQuery := Function.partialInv encode
  decodeQuery_eq_some_iff _ _ := encode_injective.isPartialInv _ _
  encodeReply _ := Function.Embedding.refl _

/-- The codec sends exactly the documented gate, query, unary-wire and service payloads. -/
@[simp] theorem codec_encodeQuery (q : DeviceRequest m Operation) :
    (codec m Operation).encodeQuery q = q.encode := by rfl

/-- Typed requests cross the word interface without changing their replies. -/
theorem codec_wordOracle_encode {M : Type → Type} [Monad M]
    (oracle : DeviceRequest m Operation → M (List Bool)) (q : DeviceRequest m Operation) :
    (codec m Operation).wordOracle oracle q.encode = id <$> oracle q := by
  exact OracleCodec.wordOracle_encodeQuery _ _ _

/-- One selected quantum operation costs one; all other operations cost zero. -/
@[expose] def operationCost (operation : DeviceOperation) :
    (DeviceOperation ⊕ Operation) × List Bool → ℕ
  | (.inl tag, _) => if tag = operation then 1 else 0
  | (.inr _, _) => 0

/-- Classical service calls have their own cost, independent of the quantum operations. -/
@[expose] def serviceCost : (DeviceOperation ⊕ Operation) × List Bool → ℕ
  | (.inl _, _) => 0
  | (.inr _, _) => 1

/-- The four independent costs partition all requests, including rejected attempts. -/
theorem operationCost_sum (request : (DeviceOperation ⊕ Operation) × List Bool) :
    operationCost .gate request + operationCost .query request +
      operationCost .measure request + serviceCost request = 1 := by
  rcases request with ⟨tag, word⟩
  rcases tag with tag | tag
  · cases tag <;> rfl
  · rfl

/-- Each selected operation count is bounded by the total number of requests. -/
theorem operationCost_le_one (operation : DeviceOperation)
    (request : (DeviceOperation ⊕ Operation) × List Bool) :
    operationCost operation request ≤ 1 := by
  rcases request with ⟨tag, word⟩
  rcases tag with tag | tag
  · change (if tag = operation then 1 else 0) ≤ 1
    split_ifs <;> omega
  · exact Nat.zero_le 1

/-- Service calls are bounded by the total number of requests. -/
theorem serviceCost_le_one (request : (DeviceOperation ⊕ Operation) × List Bool) :
    serviceCost request ≤ 1 := by
  rcases request with ⟨tag, word⟩
  rcases tag with tag | tag <;> simp [serviceCost]

end DeviceRequest

end Cslib.Quantum
