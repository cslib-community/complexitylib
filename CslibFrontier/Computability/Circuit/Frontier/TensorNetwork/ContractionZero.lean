/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Explicit
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# A zero vertex annihilates a described contraction

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.contraction_eq_zero_of_vertex`: a vertex whose entry
  vanishes at every word makes every term of the contraction zero.
-/

public section

namespace Cslib.Circuits.Frontier.DescribedNetwork

/-- A zero vertex annihilates the contraction, without any graph-shape or port-validity premise. -/
theorem contraction_eq_zero_of_vertex {T R : Type*} [CommSemiring R]
    (G : DescribedNetwork T) (entry : T → List Bool → R) {v : List ℕ × T}
    (hv : v ∈ G.vertices) (hz : ∀ bs, entry v.2 bs = 0) : G.contraction entry = 0 := by
  unfold contraction
  apply Finset.sum_eq_zero
  intro x _
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨v, hv, hz _⟩

end Cslib.Circuits.Frontier.DescribedNetwork
