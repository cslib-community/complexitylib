/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.PermutationCycles

/-!
# Boolean potentials along actual face cycles

A face-even edge labeling is a difference of a Boolean potential at consecutive **darts**
of the face permutation. This holds for every indexed rotation, including positive genus.
These potentials are not vertex spins. The forward proof supplies actual finite permutation
cycle graphs with internally proved numerical genus zero; no lifting provider is assumed.
The reverse implication is telescoping on the full face quotient, including singleton faces.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- Face-even labels have potentials on consecutive indexed face darts, with no genus or
endpoint-declaration hypothesis. A dart potential need not descend to graph vertices. -/
theorem exists_facePotential_of_faceEven {G : Graph} (r : RotationSystem G)
    (x : Fin G.2.length → Bool) (hx : r.FaceEven x) :
    ∃ p : Dart G → Bool, ∀ d, x d.1 = (p d ^^ p (r.faceNext d)) := by
  classical
  let e := Dart.indexEquiv G
  let f := e.permCongr r.faceNext
  let y (i : Fin (2 * G.2.length)) := x (e.symm i).1
  have hsame (i : Fin (2 * G.2.length)) (d : Dart G) :
      f.SameCycle i (e d) ↔ r.faceNext.SameCycle (e.symm i) d := by
    simpa only [Equiv.apply_symm_apply] using
      (Perm.sameCycle_equiv_iff e r.faceNext f (fun d => by simp [f]) (e.symm i) d)
  have hsum (i : Fin (2 * G.2.length)) :
      (∑ j : Fin (2 * G.2.length), if f.SameCycle i j then y j else 0) = 0 := by
    rw [← Equiv.sum_comp e]
    simp only [hsame, y, Equiv.symm_apply_apply]
    have h := hx (Quotient.mk _ (e.symm i))
    rw [r.faceParity_mk, parityOn_eq_sum, Finset.sum_filter] at h
    simpa only [Bool.zero_eq_false] using h
  obtain ⟨p, hp⟩ := exists_potential_of_cycleSum_zero f y hsum
  refine ⟨fun d => p (e d), fun d => ?_⟩
  have h := hp (e d)
  simpa only [y, f, Equiv.symm_apply_apply, Equiv.permCongr_apply] using h

/-- Differences of consecutive face-dart potentials telescope on every full face orbit.
This implication also needs neither numerical genus nor declared endpoints. -/
theorem faceEven_of_facePotential {G : Graph} (r : RotationSystem G)
    (x : Fin G.2.length → Bool) (p : Dart G → Bool)
    (hp : ∀ d, x d.1 = (p d ^^ p (r.faceNext d))) : r.FaceEven x := by
  classical
  intro face
  have hs := Equiv.sum_comp r.faceNext (fun d : Dart G =>
    if (Quotient.mk _ d : r.Face) = face then p d else (0 : Bool))
  simp only [r.face_eq_next] at hs
  calc
    r.faceParity x face = ∑ d : Dart G,
        if (Quotient.mk _ d : r.Face) = face then (p d + p (r.faceNext d)) else 0 := by
      rw [faceParity, parityOn_eq_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      rw [hp d, ← Bool.add_eq_xor]
    _ = (∑ d : Dart G, if (Quotient.mk _ d : r.Face) = face then p d else 0) +
        ∑ d : Dart G, if (Quotient.mk _ d : r.Face) = face then p (r.faceNext d) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = false := by
      rw [hs]
      simpa only [Bool.zero_eq_false] using BooleanRing.add_self
        (∑ d : Dart G, if (Quotient.mk _ d : r.Face) = face then p d else 0)

end Cslib.Complexity.Graph.RotationSystem
