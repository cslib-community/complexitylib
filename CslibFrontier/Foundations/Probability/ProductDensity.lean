/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PairwiseIndependentHash
import CslibFrontier.Foundations.Data.Finset.Density
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
# Marginal densities in finite products

Coordinate events preserve their marginal density; events on distinct coordinates are
independent. These reuse seed relabelling and the existing two-factor density identity.
-/

public section

namespace Cslib.Probability
open Finset

/-- **Independence of separate seeds**: on the product of two seed spaces, an event about the
first seed and an event about the second have probability equal to the product of their
probabilities. -/
theorem dens_filter_fst_and_snd {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → Prop)
    (q : κ → Prop) [DecidablePred p] [DecidablePred q] :
    dens {z : ι × κ | p z.1 ∧ q z.2} = dens {i | p i} * dens {j | q j} := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card, dens_eq_card_div_card,
    ← univ_product_univ, filter_product, card_product, Fintype.card_prod]
  push_cast
  rw [mul_div_mul_comm]

/-- A coordinate of a uniform finite product has its original marginal density. -/
theorem dens_filter_pi_eval {Role A : Type} [Fintype Role] [DecidableEq Role]
    [Fintype A] [Nonempty A] (role : Role) (E : A → Prop) [DecidablePred E] :
    dens {σ : Role → A | E (σ role)} = dens {a | E a} := by
  classical
  have h := Fintype.dens_filter_comp_equiv
    (Equiv.piSplitAt role (fun _ : Role => A)) (fun z => E z.1)
  have hp := dens_filter_fst_and_snd E (fun _ : {j : Role // j ≠ role} → A => True)
  simpa using h.trans (by simpa using hp)

/-- Distinct actual role coordinates are independent under uniform product density. -/
theorem dens_filter_pi_eval_and_pi_eval {Role A : Type} [Fintype Role] [DecidableEq Role]
    [Fintype A] [Nonempty A] {i j : Role} (hij : j ≠ i)
    (E F : A → Prop) [DecidablePred E] [DecidablePred F] :
    dens {σ : Role → A | E (σ i) ∧ F (σ j)} = dens {a | E a} * dens {a | F a} := by
  classical
  let G : ({k : Role // k ≠ i} → A) → Prop := fun σ => F (σ ⟨j, hij⟩)
  have h := Fintype.dens_filter_comp_equiv
    (Equiv.piSplitAt i (fun _ : Role => A)) (fun z => E z.1 ∧ G z.2)
  change dens {σ : Role → A | E (σ i) ∧ F (σ j)} = _ at h
  rw [h, dens_filter_fst_and_snd, dens_filter_pi_eval]

end Cslib.Probability
