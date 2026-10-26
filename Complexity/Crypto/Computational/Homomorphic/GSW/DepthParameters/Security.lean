/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters
public import Complexity.Crypto.Computational.Homomorphic.GSW.Security

/-!
# Security for the GSW family with a growing noise budget

The explicit depth-compatible family supplies the native dimension routines and entropy surplus
required by the actual-algorithm security reduction. Its exact decision-LWE assumption remains a
hypothesis; hardness for the earlier parameter family does not establish hardness for this one.
No decryption-circuit, bootstrappability or circular-security premise is hidden here.

## Main results

* `DepthParameters.indCPA`: actual serialized encryption security under this family's exact LWE.

## References

* [Gentry, Sahai and Waters, Sections 3.1–3.2][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.DepthParameters

open Parameters (dimension noise)

/-- The actual serialized algorithms are IND-CPA under decision LWE for this exact new family.
The LWE premise for the earlier, narrower modulus family is not used. -/
theorem indCPA
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k))) :
    Encryption.INDCPA
      (fun k => keyGenSerialized (dimension k) (samples k) (width k) (noise k))
      (fun k => encryptSerialized (dimension k) (samples k) (width k)) :=
  indCPA_of_decisionLWE Parameters.computableInPolyTime_dimension
    DepthParameters.computableInPolyTime_samples DepthParameters.computableInPolyTime_width
    (Filter.Eventually.of_forall entropy_margin) hLWE

end Cslib.Crypto.Homomorphic.GSW.DepthParameters
