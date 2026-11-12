/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star

/-! Unbounded ordered atom-star rotation and the isolated nullary center. -/

namespace CslibFrontierTests.RotationStar

open Cslib.Complexity Graph.RotationSystem

example : Graph.RotationCertificate.ofRotation (starRotation 0) = ⟨[]⟩ := by decide +kernel

example : Graph.RotationCertificate.ofRotation (starRotation 1) = ⟨[0, 1]⟩ := by decide +kernel

example : Graph.RotationCertificate.ofRotation (starRotation 5) =
    ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero (starGraph 0) ⟨[]⟩ = true := by decide

example : Graph.RotationCertificate.verifyGenusZero (starGraph 5)
    ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩ = true := by decide

example : (starRotation 31).NumericalGenusZero := numericalGenusZero_starRotation 31

end CslibFrontierTests.RotationStar
