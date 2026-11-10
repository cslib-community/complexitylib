/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Sums and products of natural numbers

A finite sum of `m i - 1` over positive natural numbers is at most `∏ m i - 1`
(`Nat.sum_sub_one_le_prod_sub_one`). The CRT reconstruction of
`CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/CRT.lean` uses it to bound a linear combination
of residues.

## Main results

* `Nat.sum_sub_one_le_prod_sub_one`: `∑ i ∈ t, (m i - 1) ≤ ∏ i ∈ t, m i - 1` when every `m i` is
  positive.
-/

public section

namespace Nat

/-- For positive `m i`, the sum of the `m i - 1` is at most the product of the `m i`, minus one. -/
theorem sum_sub_one_le_prod_sub_one {ι : Type*} (t : Finset ι) {m : ι → ℕ}
    (hm : ∀ i ∈ t, 0 < m i) : ∑ i ∈ t, (m i - 1) ≤ ∏ i ∈ t, m i - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih := ih fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hP : 0 < ∏ i ∈ t, m i := Finset.prod_pos fun j hj => hm j (Finset.mem_insert_of_mem hj)
    have ha' := hm a (Finset.mem_insert_self a t)
    have key : m a + ∏ i ∈ t, m i ≤ m a * ∏ i ∈ t, m i + 1 := by nlinarith
    omega

end Nat
