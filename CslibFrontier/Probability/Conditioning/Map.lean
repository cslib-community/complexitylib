/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF.Map

/-!
# Mapping the hidden component of a conditional distribution

A deterministic map of the second component commutes with conditioning on a
supported first component. The map may forget hidden state, and the discrete
types need not be finite. The proof reuses joint reconstruction and recovery of
a supported conditional kernel, without another normalization argument.

## Main results

* `conditionalSnd_map_snd`: map the hidden component before or after conditioning.
-/

public section
noncomputable section
namespace Cslib.Probability.PMF
variable {α β δ : Type*}

/-- Relabeling or forgetting the hidden component preserves its conditional law
at every supported observation of the unchanged first component. -/
theorem conditionalSnd_map_snd (joint : PMF (α × β)) (f : β → δ) (a : α)
    (ha : a ∈ (joint.map Prod.fst).support) :
    conditionalSnd (joint.map (fun pair => (pair.1, f pair.2))) a =
      (conditionalSnd joint a).map f := by
  have he : joint.map (fun pair => (pair.1, f pair.2)) =
      (joint.map Prod.fst).bind (fun x => ((conditionalSnd joint x).map f).map (x, ·)) := by
    conv =>
      lhs
      rw [← bind_conditionalSnd joint]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [he, conditionalSnd_bind_pair _ _ a ha]

end Cslib.Probability.PMF
