/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import Mathlib.Data.List.GetD

/-!
# Literal successor tables for a selected outgoing-corner swap

The raw list program is funded by the supplied table length, including malformed inputs.
For the actual vertex-identification rotation it is exactly the generated successor table.
Only the selected outgoing entries are exchanged; the internal order of both forward blocks
is retained. These original identities make no genus claim for arbitrary selected corners.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

/-- Exchange two outgoing entries in the supplied successor table. Every iteration is funded
by the list length; missing selected indices use the ordinary raw-table fallback zero. -/
@[expose] def swapSuccessors (c : RotationCertificate) (h k : ℕ) : RotationCertificate :=
  ⟨(List.range c.successor.length).map fun i =>
    c.successor.getD (if i = h then k else if i = k then h else i) 0⟩

/-- The raw outgoing swap retains the entire supplied table length, including zero. -/
theorem length_swapSuccessors (c : RotationCertificate) (h k : ℕ) :
    (swapSuccessors c h k).successor.length = c.successor.length := by
  simp [swapSuccessors]

/-- Every actual retained position has its explicitly selected old successor. No validity
premise is imposed on the input table or its binary entries. -/
theorem getD_swapSuccessors (c : RotationCertificate) (h k i : ℕ)
    (hi : i < c.successor.length) :
    (swapSuccessors c h k).successor.getD i 0 =
      c.successor.getD (if i = h then k else if i = k then h else i) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [length_swapSuccessors]; exact hi)]
  simp only [swapSuccessors, List.getElem_map, List.getElem_range]

end Cslib.Complexity.Graph.RotationCertificate

namespace Cslib.Complexity.Graph.RotationSystem

/-- The constructed vertex-identification rotation encodes to exactly one outgoing-table
swap. This is an equality of complete finite tables, not just their signatures or acceptance. -/
theorem ofRotation_mergeVertices {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    RotationCertificate.ofRotation (r.mergeVertices h k hk) =
      (RotationCertificate.ofRotation r).swapSuccessors h.index k.index := by
  apply (RotationCertificate.ofRotation_eq_iff _ _).mpr
  constructor
  · rw [RotationCertificate.length_swapSuccessors, RotationCertificate.length_ofRotation]
    simp [mergeGraph, Graph.relabel]
  · intro a
    obtain ⟨d, rfl⟩ := (mergeDartEquiv h k).surjective a
    have hi : d.index < (RotationCertificate.ofRotation r).successor.length := by
      rw [RotationCertificate.length_ofRotation]
      exact (Dart.indexEquiv G d).isLt
    have hj (a b : Dart G) : a.index = b.index ↔ a = b := by
      constructor
      · intro he
        exact (Dart.indexEquiv G).injective (Fin.ext he)
      · exact congrArg Dart.index
    rw [show (mergeDartEquiv h k d).index = d.index from rfl,
      RotationCertificate.getD_swapSuccessors _ _ _ _ hi]
    simp only [hj, rotate_mergeVertices, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.Perm.coe_mul, Function.comp_apply]
    by_cases hd : d = h
    · subst d
      simp only [ite_true, Equiv.swap_apply_left, RotationCertificate.getD_ofRotation]
      rfl
    · by_cases he : d = k
      · subst d
        simp only [hd, ite_false, ite_true, Equiv.swap_apply_right,
          RotationCertificate.getD_ofRotation]
        rfl
      · simp only [hd, he, ite_false, Equiv.swap_apply_of_ne_of_ne hd he,
          RotationCertificate.getD_ofRotation]
        rfl

end Cslib.Complexity.Graph.RotationSystem
