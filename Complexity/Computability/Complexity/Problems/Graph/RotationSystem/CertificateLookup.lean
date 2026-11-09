/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Exact generated certificates from all actual dart lookups

The canonical finite successor list is determined by its length and the successor at each
indexed edge end. These original list identities allow inspection after nontrivial dart
transport without evaluating an inverse chosen by a structural equivalence.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

/-- A raw table is the exact canonical generated certificate iff it has the actual dart
count and agrees with every literal successor, including the empty-graph case. -/
theorem ofRotation_eq_iff {G : Graph} (r : RotationSystem G) (c : RotationCertificate) :
    ofRotation r = c ↔ c.successor.length = 2 * G.2.length ∧
      ∀ d : Dart G, c.successor.getD d.index 0 = (r.rotate d).index := by
  constructor
  · rintro rfl
    exact ⟨length_ofRotation r, getD_ofRotation r⟩
  · rintro ⟨hlen, hstep⟩
    apply congrArg RotationCertificate.mk
    refine List.ext_getElem (by
      change (ofRotation r).successor.length = c.successor.length
      rw [length_ofRotation, hlen]) ?_
    intro i hi hj
    change i < (ofRotation r).successor.length at hi
    change (ofRotation r).successor[i] = c.successor[i]
    rw [← List.getD_eq_getElem (ofRotation r).successor 0 hi,
      ← List.getD_eq_getElem c.successor 0 hj]
    have hb : i < 2 * G.2.length := by rwa [length_ofRotation] at hi
    let d := (Dart.indexEquiv G).symm ⟨i, hb⟩
    have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hb⟩)
    rw [← hd, getD_ofRotation, hstep]

end Cslib.Complexity.Graph.RotationCertificate
