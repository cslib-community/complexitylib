/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Nechiporuk
public import Complexity.Foundations.Data.BitString.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Bitwise

/-!
# Nechiporuk's bound for element distinctness

*Element distinctness* reads `m` blocks of `k` bits and says whether the blocks are pairwise
different (`elementDistinctness`). With blocks of `2 t` bits and `m ≤ 2 ^ t`, it has at least
`2 ^ (t (m - 1))` subfunctions on each block: give the other blocks the values `(j, wⱼ)`, tagged by
their position `j`, and each choice of the `wⱼ` is told apart by its own set of forbidden values
for the remaining block. Nechiporuk's bound then shows that a formula for it of leaf size `L` over
any basis of fan-in at most two, such as the full binary basis, has `m (m - 1) t ≤ 4 L + m`
(`mul_le_leafSize_of_computes_elementDistinctness`) [Nechiporuk1966],
[Jukna, Section 6.5][Jukna2012]. Taking `t = ⌈log₂ m⌉`
(`mul_clog_le_leafSize_of_computes_elementDistinctness`), the `n = 2 m ⌈log₂ m⌉` bits need leaf
size about `m ^ 2 log₂ m / 4`, which is of order `n ^ 2 / log n`.

## Main definitions

* `Cslib.Circuits.Boolean.elementDistinctness`: whether `m` blocks of `k` bits are distinct.

## Main results

* `Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness`: Nechiporuk's bound for
  element distinctness.

## References

* [E. I. Nechiporuk, *On a Boolean function*][Nechiporuk1966]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset
open BitString (block blockBits block_piecewise pairwiseDisjoint_blockBits subfunctions
  mem_subfunctions)

variable {m k t : ℕ}

namespace ElementDistinctness

/-- `t` bits naming a position `j < 2 ^ t`. -/
private def tag (t j : ℕ) : Fin t → Bool :=
  fun b => j.testBit b

private theorem tag_injective (hm : m ≤ 2 ^ t) : Function.Injective fun j : Fin m => tag t j := by
  intro i j h
  refine Fin.ext (Nat.eq_of_testBit_eq fun b => ?_)
  by_cases hb : b < t
  · exact congrFun h ⟨b, hb⟩
  · have hbt : 2 ^ t ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (i.isLt.trans_le (hm.trans hbt)),
      Nat.testBit_eq_false_of_lt (j.isLt.trans_le (hm.trans hbt))]

/-- The assignment giving block `j` the value `(j, w j)`. -/
private def tagged (w : Fin m → Fin t → Bool) : BitString (m * (t + t)) :=
  fun p => Fin.append (tag t (finProdFinEquiv.symm p).1) (w (finProdFinEquiv.symm p).1)
    (finProdFinEquiv.symm p).2

private theorem block_tagged (w : Fin m → Fin t → Bool) (j : Fin m) :
    block (tagged w) j = Fin.append (tag t j) (w j) := by
  funext b
  simp [block, tagged]

end ElementDistinctness

open ElementDistinctness

/-- Element distinctness: whether the `m` blocks of `k` bits are pairwise different. -/
def elementDistinctness (m k : ℕ) : BooleanFunction (m * k) :=
  fun x => decide (Function.Injective (block x))

/-- Element distinctness has at least `2 ^ (t (m - 1))` subfunctions on each block of `2 t` bits
when `m ≤ 2 ^ t`. -/
private theorem two_pow_le_card_subfunctions_elementDistinctness (hm : m ≤ 2 ^ t) (i : Fin m) :
    2 ^ (t * (m - 1)) ≤ #(subfunctions (elementDistinctness m (t + t)) (blockBits (t + t) i)) := by
  -- Give block `j ≠ i` the value `(j, u j)`.
  let w (u : {j // j ≠ i} → Fin t → Bool) : Fin m → Fin t → Bool :=
    fun j => if h : j = i then fun _ => false else u ⟨j, h⟩
  let val (u : {j // j ≠ i} → Fin t → Bool) (j : Fin m) : Fin (t + t) → Bool :=
    Fin.append (tag t j) (w u j)
  have htag {u u' : {j // j ≠ i} → Fin t → Bool} {j j' : Fin m} (h : val u j = val u' j') :
      j = j' :=
    tag_injective hm (funext fun c => by simpa [val] using congrFun h (Fin.castAdd t c))
  let g (u : {j // j ≠ i} → Fin t → Bool) : BooleanFunction (m * (t + t)) :=
    fun x => elementDistinctness m (t + t) ((blockBits (t + t) i).piecewise x (tagged (w u)))
  have hg (u : {j // j ≠ i} → Fin t → Bool) (x : BitString (m * (t + t))) :
      g u x = decide (Function.Injective fun j => if j = i then block x j else val u j) := by
    have h : block ((blockBits (t + t) i).piecewise x (tagged (w u))) =
        fun j => if j = i then block x j else val u j := by
      funext j
      rw [block_piecewise, block_tagged]
    simp only [g, elementDistinctness, h]
  have hinj : Set.InjOn g (univ : Finset ({j // j ≠ i} → Fin t → Bool)) := by
    intro u _ u' _ huu
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    -- The value of block `j` under `u` is not the value of any other block under `u'`.
    have key (l : Fin m) (hl : l ≠ i) (h : val u j = val u' l) : False := by
      obtain rfl := htag h
      refine hj (funext fun c => ?_)
      have hc := congrFun h (Fin.natAdd t c)
      simp only [val] at hc
      rw [Fin.append_right, Fin.append_right] at hc
      simpa [w, j.2] using hc
    -- An input whose block `i` repeats block `j` of the first assignment.
    let x : BitString (m * (t + t)) := fun p => val u j (finProdFinEquiv.symm p).2
    have hx : ∀ l, block x l = val u j := fun l => funext fun b => by
      simp only [x, block, Equiv.symm_apply_apply]
    have h₁ : g u x = false := by
      rw [hg, decide_eq_false_iff_not]
      intro h
      exact j.2 (@h i j (by simp [hx, val, w, j.2])).symm
    have h₂ : g u' x = true := by
      rw [hg, decide_eq_true_iff]
      intro l₁ l₂ h
      by_cases h₁ : l₁ = i <;> by_cases h₂ : l₂ = i
      · exact h₁.trans h₂.symm
      · simp only [h₁, h₂, ↓reduceIte, hx] at h
        exact (key l₂ h₂ h).elim
      · simp only [h₁, h₂, ↓reduceIte, hx] at h
        exact (key l₁ h₁ h.symm).elim
      · simpa [h₁, h₂] using htag (u := u') (u' := u') (by simpa [h₁, h₂] using h)
    exact absurd (congrFun huu x) (by rw [h₁, h₂]; decide)
  have hcard : Fintype.card ({j // j ≠ i} → Fin t → Bool) = 2 ^ (t * (m - 1)) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique, pow_mul]
  rw [← hcard, ← card_univ]
  exact card_le_card_of_injOn g (fun u _ => mem_subfunctions.2 ⟨tagged (w u), rfl⟩) hinj

/-- **Nechiporuk's bound for element distinctness.** For `m ≤ 2 ^ t`, a formula over a basis of
fan-in at most two deciding whether `m` blocks of `2 t` bits are pairwise different has leaf size
`L` with `m (m - 1) t ≤ 4 L + m`. -/
theorem mul_le_leafSize_of_computes_elementDistinctness {σ : Signature}
    (harity : ∀ op, σ.Arity op ≤ 2) {I : Interpretation σ Bool} (hm : m ≤ 2 ^ t)
    {F : Formula σ (m * (t + t))} (hF : F.Computes I (elementDistinctness m (t + t))) :
    m * (m - 1) * t ≤ 4 * F.leafSize + m := by
  have h := sum_clog_card_subfunctions_le harity hF (s := univ)
    (pairwiseDisjoint_blockBits (t + t))
  rw [card_univ, Fintype.card_fin] at h
  calc m * (m - 1) * t = ∑ _i : Fin m, t * (m - 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm t, mul_assoc]
    _ ≤ ∑ i, Nat.clog 2 #(subfunctions (elementDistinctness m (t + t)) (blockBits (t + t) i)) :=
        sum_le_sum fun i _ => (Nat.clog_pow 2 (t * (m - 1)) (by decide)).symm.trans_le
          (Nat.clog_mono_right 2 (two_pow_le_card_subfunctions_elementDistinctness hm i))
    _ ≤ 4 * F.leafSize + m := h

/-- With blocks of `2 ⌈log₂ m⌉` bits, a formula over a basis of fan-in at most two for element
distinctness of `m` blocks has leaf size `L` with `m (m - 1) ⌈log₂ m⌉ ≤ 4 L + m`. -/
theorem mul_clog_le_leafSize_of_computes_elementDistinctness {σ : Signature}
    (harity : ∀ op, σ.Arity op ≤ 2) {I : Interpretation σ Bool}
    {F : Formula σ (m * (Nat.clog 2 m + Nat.clog 2 m))}
    (hF : F.Computes I (elementDistinctness m (Nat.clog 2 m + Nat.clog 2 m))) :
    m * (m - 1) * Nat.clog 2 m ≤ 4 * F.leafSize + m :=
  mul_le_leafSize_of_computes_elementDistinctness harity (Nat.le_pow_clog (by decide) m) hF

end Cslib.Circuits.Boolean
