/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Basic

/-!
# Three-message public-coin specifications

The prover sends a commitment, the verifier sends a challenge, and the prover sends a response.
The verifier reads both prover messages in full. This shared message shape is used by Sigma
protocols and ideal VOLE checks; it carries no security or efficiency assumptions.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.sigmaSpec`: the three-message specification.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Interactive

/-- The three-round public-coin specification of a Sigma protocol with commitments in `T`,
challenges in `C` and responses in `Z`: prover commitment, verifier challenge, prover response. -/
@[expose, reducible] def sigmaSpec (T C Z : Type) : Interactive.Spec :=
  [.prover T (OracleInterface.full T), .verifier C, .prover Z (OracleInterface.full Z)]

end Cslib.Crypto.Protocols.SigmaProtocol
