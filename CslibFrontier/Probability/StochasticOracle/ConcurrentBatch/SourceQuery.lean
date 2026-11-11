/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Protocol
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat

/-!
# Addressed opaque source queries

[Wang2027], Section 3, PDF pp. 4–5. The transport address selects an original
oracle configuration; the opaque payload is its original query string. Decoding
is total and natively polynomial. The joint source sampler receives all decoded
calls before returning any response, retaining hidden state and entire trajectories.

## Main definitions

* `encoding`, `decode`: addressed query wire format and its total native decoder.
* `SourceSampler`, `adapt`: one source oracle and its concrete packet-interface adapter.

## Main results

* `decode_encode`: exact address/payload round trip for arbitrary source strings.
* `computable_decode`: native polynomial decoding without a codec certificate premise.
-/

public section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch.SourceQuery
open Turing Turing.MultiTapeTM NativeOpenExecution

/-- Binary original-oracle index, framed, followed by the unmodified query payload. -/
abbrev encoding : ℕ × Word ↪ Word := encPair encNat encBits

/-- Total decoding of transport addresses and opaque payloads. -/
@[expose] def decode : Word → ℕ × Word := (Decoder.pair Decoder.nat Decoder.bits).decode

/-- The original oracle receives exactly its own index and query bytes. -/
theorem decode_encode (call : ℕ × Word) : decode (encoding call) = call :=
  (Decoder.pair Decoder.nat Decoder.bits).decode_enc call

/-- One native polynomial decoder works for all addresses and query lengths. -/
theorem computable_decode : ComputableInPolyTime decode encBits encoding :=
  (Decoder.pair Decoder.nat Decoder.bits).computableInPolyTime

/-- One consistent source oracle, indexed by opportunity count. Calls remain
preformed and the response is a joint sample with arbitrary hidden memory. -/
abbrev SourceSampler (P : Type) := ∀ n, ServerState n P →
  (Fin n → Option (ℕ × Word)) → PMF ((Fin n → CallTrace) × P)

/-- Concrete adaptation preserves the original joint trajectories, private state,
invoices and physical call durations. Only transport commands are decoded. -/
@[expose] def adapt {P : Type} (source : SourceSampler P) (n : ℕ) : Sampler n P :=
  fun state batch => source n state fun i => (batch.slots i).map decode

end Cslib.Probability.StochasticOracle.ConcurrentBatch.SourceQuery
