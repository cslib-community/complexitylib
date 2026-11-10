/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.Conditioning

/-!
# Joint laws with an optional second outcome

The first marginal and the projection that erases the first outcome on `none` determine the
whole joint law. This recovers an aborted commitment's mass without discarding that commitment.

## Main results

* `Cslib.Probability.PMF.map_option_prod_apply_some`: erasure preserves every successful atom.
* `Cslib.Probability.PMF.ext_prod_option`: the marginal and erased projection determine the law.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- Erasing the first component only on `none` preserves every successful point mass. -/
theorem map_option_prod_apply_some {α β : Type*} (p : PMF (α × Option β)) (a : α) (b : β) :
    (p.map fun pair => pair.2.map fun b => (pair.1, b)) (some (a, b)) = p (a, some b) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (a, some b)]
  · simp
  · rintro ⟨a', _ | b'⟩ hne
    · simp
    · have hn : (a, b) ≠ (a', b') := by
        intro h
        cases h
        exact hne rfl
      simp [hn]

/-- A joint law with an optional outcome is determined by its first marginal and the law that
erases the first component on `none`. The finite total mass makes cancellation legitimate. -/
theorem ext_prod_option {α β : Type*} {p q : PMF (α × Option β)}
    (hfst : p.map Prod.fst = q.map Prod.fst)
    (herase : (p.map fun pair => pair.2.map fun b => (pair.1, b)) =
      q.map fun pair => pair.2.map fun b => (pair.1, b)) : p = q := by
  classical
  have hsome (a : α) (b : β) : p (a, some b) = q (a, some b) := by
    simpa only [map_option_prod_apply_some] using congrArg (fun law => law (some (a, b))) herase
  ext ⟨a, b⟩
  cases b with
  | some b => exact hsome a b
  | none =>
    have h := congrArg (fun law => law a) hfst
    simp only [map_fst_apply] at h
    rw [tsum_eq_add_tsum_ite (f := fun b => p (a, b)) none,
      tsum_eq_add_tsum_ite (f := fun b => q (a, b)) none] at h
    have hfinite : (∑' b, if b = none then 0 else q (a, b)) ≠ (⊤ : ℝ≥0∞) := by
      apply ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      calc
        _ ≤ ∑' b, q (a, b) := tsum_le_tsum fun b => by split_ifs <;> simp
        _ = (q.map Prod.fst) a := (map_fst_apply q a).symm
        _ ≤ 1 := PMF.coe_le_one _ _
    apply (ENNReal.add_left_inj hfinite).mp
    convert h using 2 <;> apply tsum_congr <;> intro b <;> cases b <;> simp [hsome]

end Cslib.Probability.PMF
