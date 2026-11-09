/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomially balanced images of PSPACE languages

A bounded search for a source word transfers polynomial space along a polynomial-time function.
The function need not be injective and no efficient inverse is assumed. The source-length bound
is required only on accepted source words. This generalizes the application-specific argument in
`lean-canny` at revision `12ea037`, using the existing plain machine interfaces.
## Main results

* `Cslib.Complexity.bounded_image_mem_PSPACE`: polynomially balanced images preserve PSPACE,
  without injectivity or an efficient inverse.

-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The image of a PSPACE language under a polynomial-time function is in PSPACE when accepted
source words have a polynomial-time unary length bound computed from their images. -/
theorem bounded_image_mem_PSPACE {L : Set (List Bool)} {f : List Bool → List Bool}
    (hL : L ∈ PSPACE encBits) (hf : ComputableInPolyTime f encBits encBits)
    {bound : List Bool → ℕ} (hb : ComputableInPolyTime bound encBits encUnary)
    (hbalance : ∀ w ∈ L, w.length ≤ bound (f w)) : f '' L ∈ PSPACE encBits := by
  have hc : ComputableInPolyTime (fun p : List Bool × List Bool => unframe p.2)
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.unframe.comp (ComputableInPolyTime.snd _ _)
  have hsource : {p : List Bool × List Bool | unframe p.2 ∈ L} ∈
      PSPACE (encPair encBits encBits) :=
    PolyTimeReducible.mem_PSPACE ⟨_, hc, fun _ => Iff.rfl⟩ hL
  have heq : {p : List Bool × List Bool | f (unframe p.2) = p.1} ∈
      P (encPair encBits encBits) :=
    ⟨fun p => decide (f (unframe p.2) = p.1),
      ComputableInPolyTime.decide_eq' (hf.comp hc) (ComputableInPolyTime.fst _ _),
      fun _ => by simp⟩
  have htest := inter_mem_PSPACE hsource (P_subset_PSPACE heq)
  have hwidth : ComputableInPolyTime (fun y => 2 * bound y + 1) encBits encUnary := by
    fun_prop
  have hsearch := setOf_exists_mem_PSPACE htest hwidth
  convert hsearch using 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    let padding := List.replicate (2 * bound (f w) - 2 * w.length) false
    refine ⟨frame w ++ padding, ?_, ?_, ?_⟩
    · have hlen := hbalance w hw
      simp only [List.length_append, length_frame, padding, List.length_replicate]
      omega
    · simpa only [unframe_frame_append] using hw
    · simp only [unframe_frame_append]
  · rintro ⟨w, _, hw, he⟩
    exact ⟨unframe w, hw, he⟩

end Cslib.Complexity
