/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport
import Mathlib.Data.List.GetD

/-!
# Predecessors in accepted raw successor tables

The predecessor of an actual dart is computed by finding its index in the supplied successor
list. The scan is funded by that list and never by a binary entry. These original identities
connect inverse rotations used in proofs to literal finite certificate programs.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

/-- The inverse of a supplied abstract rotation is read by one positional search in its
canonical table. This includes singleton vertex cycles and requires an actual dart. -/
theorem idxOf_ofRotation {G : Graph} (r : RotationSystem G) (d : Dart G) :
    (ofRotation r).successor.idxOf d.index = (r.rotate.symm d).index := by
  have hi : Function.Injective (fun i : Fin (2 * G.2.length) =>
      (r.rotate ((Dart.indexEquiv G).symm i)).index) := by
    intro i j he
    apply (Dart.indexEquiv G).symm.injective
    apply r.rotate.injective
    exact (Dart.indexEquiv G).injective (Fin.ext he)
  have hn : (ofRotation r).successor.Nodup := List.nodup_ofFn.mpr hi
  have hk : (r.rotate.symm d).index < (ofRotation r).successor.length := by
    rw [length_ofRotation]
    exact (Dart.indexEquiv G (r.rotate.symm d)).isLt
  have he : (ofRotation r).successor[(r.rotate.symm d).index] = d.index := by
    rw [← List.getD_eq_getElem _ 0 hk, getD_ofRotation, Equiv.apply_symm_apply]
  rw [← he]
  exact hn.idxOf_getElem _ _

/-- For any accepted raw table, its actual inverse rotation is exactly the bounded list
search for the given dart index. Empty graphs have no dart premise to manufacture. -/
theorem index_decode_rotate_symm {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    ((decode G c h).rotate.symm d).index = c.successor.idxOf d.index := by
  calc
    _ = (ofRotation (decode G c h)).successor.idxOf d.index :=
      (idxOf_ofRotation (decode G c h) d).symm
    _ = c.successor.idxOf d.index :=
      congrArg (fun t : RotationCertificate => t.successor.idxOf d.index) (ofRotation_decode h)

end Cslib.Complexity.Graph.RotationCertificate
