/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.Blocks

/-!
# Disjoint index intervals of compiled clause blocks

Local positive auxiliary names carry an index in their original signed clause block. Adding
the preceding signed-block lengths gives disjoint intervals for distinct original clauses.

## Main results

* `PositiveExactOne.blockOffset_mono`, `PositiveExactOne.blockOffset_succ`.
* `PositiveExactOne.blockOffset_range_injective`: a global index identifies its block and slot.
* `PositiveExactOneCompile.signedOffset_range_injective`: the actual compiler specialization.

## References

These are original list-index identities for the explicit compiler.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PositiveExactOne

variable {V : Type*}

/-- Prefix lengths are monotone, without requiring the blocks to be nonempty. -/
theorem blockOffset_mono (bs : List (CNF V)) {i j : ℕ} (hij : i ≤ j) :
    blockOffset bs i ≤ blockOffset bs j := by
  unfold blockOffset
  conv_rhs => rw [show j = i + (j - i) by omega]
  rw [List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- Passing an existing block adds exactly its number of signed clauses. -/
theorem blockOffset_succ (bs : List (CNF V)) {i : ℕ} (hi : i < bs.length) :
    blockOffset bs (i + 1) = blockOffset bs i + bs[i].length := by
  simp only [blockOffset, List.take_succ_eq_append_getElem hi, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Local index ranges of different blocks are disjoint. No positive-length assumption on
unrelated blocks is needed. -/
theorem blockOffset_range_injective (bs : List (CNF V)) {i j a b : ℕ}
    (hi : i < bs.length) (hj : j < bs.length) (ha : a < bs[i].length)
    (hb : b < bs[j].length) (he : blockOffset bs i + a = blockOffset bs j + b) :
    i = j ∧ a = b := by
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · have hm := blockOffset_mono bs (show i + 1 ≤ j by omega)
      rw [blockOffset_succ bs hi] at hm
      omega
    · exact hij
    · have hm := blockOffset_mono bs (show j + 1 ≤ i by omega)
      rw [blockOffset_succ bs hj] at hm
      omega
  subst j
  exact ⟨rfl, by omega⟩

end Cslib.Logic.PL.CNF.PositiveExactOne

namespace Cslib.Logic.PL.CNF.PositiveExactOneCompile

variable {V : Type*}

/-- In the actual compiler, a positive auxiliary's global signed-clause position uniquely
identifies its original clause block and local signed-clause position. -/
theorem signedOffset_range_injective (φ : CNF V) {i j a b : ℕ}
    (hi : i < φ.length) (hj : j < φ.length)
    (ha : a < (FromSAT.clause i φ[i]).length)
    (hb : b < (FromSAT.clause j φ[j]).length)
    (he : signedOffset φ i + a = signedOffset φ j + b) : i = j ∧ a = b := by
  let bs := φ.zipIdx.map fun c => FromSAT.clause c.2 c.1
  have hi' : i < bs.length := by simpa [bs] using hi
  have hj' : j < bs.length := by simpa [bs] using hj
  have ha' : a < bs[i].length := by simpa [bs] using ha
  have hb' : b < bs[j].length := by simpa [bs] using hb
  exact PositiveExactOne.blockOffset_range_injective bs hi' hj' ha' hb' he

end Cslib.Logic.PL.CNF.PositiveExactOneCompile
