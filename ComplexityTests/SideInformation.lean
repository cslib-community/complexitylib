/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.ProductConditioning.SideInformation

/-! # Holenstein's Corollary 4.3

Without a conditioning variable or side information, Corollary 4.3 specializes to Raz's
conditioning lemma; and the side-information form applies to any joint distribution with a product
first marginal, including two fair bits conditioned on the first bit being `true`.
-/

namespace ComplexityTests.SideInformation

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF

-- With trivial `T` and `V`, Corollary 4.3 bounds the coordinate distances of a conditioned product.
example {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, Fintype (β i)] (p : ∀ i, PMF (β i))
    (W : Set ((Unit × Unit) × (∀ i, β i)))
    (hW : ∃ x ∈ W, x ∈ (sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).support) :
    ∑ j, dist (((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).filter W hW).map
          fun z => (z.1, z.2 j))
        ((((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).filter W hW).map Prod.fst).bind
          fun s => (p j).map (s, ·)) ≤
      Real.sqrt (Fintype.card ι * Real.log (Fintype.card Unit /
        ((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).toOuterMeasure W).toReal) / 2) :=
  sum_dist_filter_sideJoint_le (PMF.pure ()) (fun i _ => p i) (fun _ => (pi p).map (·, ()))
    (fun _ => by rw [PMF.map_comp]; exact PMF.map_id _) W hW

/-- Two fair bits. -/
noncomputable def bits : Fin 2 → PMF Bool := fun _ => uniformOfFintype Bool

/-- Two fair bits with trivial conditioning variable and side information. -/
noncomputable def bitsJoint : PMF ((Unit × Unit) × (Fin 2 → Bool)) :=
  sideJoint (PMF.pure ()) fun _ => (pi bits).map (·, ())

theorem first_true_mem_bitsJoint :
    ∃ x ∈ {x : (Unit × Unit) × (Fin 2 → Bool) | x.2 0 = true}, x ∈ bitsJoint.support := by
  refine ⟨(((), ()), fun _ => true), rfl, ?_⟩
  rw [PMF.mem_support_iff, bitsJoint, sideJoint_apply]
  refine mul_ne_zero (by simp) ?_
  rw [← PMF.mem_support_iff, PMF.support_map]
  refine ⟨fun _ => true, ?_, rfl⟩
  rw [mem_support_pi_iff]
  intro i
  simp [bits]

-- Conditioning two fair bits on the first bit being `true` under `sideJoint`.
example :
    ∑ j, dist ((bitsJoint.filter {x | x.2 0 = true} first_true_mem_bitsJoint).map
          fun z => (z.1, z.2 j))
        (((bitsJoint.filter {x | x.2 0 = true} first_true_mem_bitsJoint).map Prod.fst).bind
          fun s => (bits j).map (s, ·)) ≤
      Real.sqrt (2 * Real.log (1 / (bitsJoint.toOuterMeasure {x | x.2 0 = true}).toReal) / 2) := by
  simpa [bitsJoint] using
    sum_dist_filter_sideJoint_le (PMF.pure ()) (fun i _ => bits i)
      (fun _ => (pi bits).map (·, ())) (fun _ => by rw [PMF.map_comp]; exact PMF.map_id _)
      {x | x.2 0 = true} first_true_mem_bitsJoint

end ComplexityTests.SideInformation
