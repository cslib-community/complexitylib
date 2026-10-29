/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Add
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanStep

/-!
# Actual native selection and accumulation of one query

## Main results

* `PrunedQuery.exec_accumulateDispatch`: the real digit comparisons select a child's addition.
* `PrunedQuery.exec_accumulateStep`: include the source indexing, load, digit and counter work.

The child-value memory premise is needed only for selected queries. Unselected child-directory
cells may contain arbitrary prior values and are never loaded by the program.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Registers changed by selected signed accumulation or its unselected no-op. -/
def AccumulateDispatchLocal (i : Fin registers) : Prop := AddValueLocal i ∨ i = temporary

instance (i : Fin registers) : Decidable (AccumulateDispatchLocal i) :=
  inferInstanceAs (Decidable (AddValueLocal i ∨ i = temporary))

private theorem accumulateDispatch_preserves (i : Fin registers) :
    ¬AccumulateDispatchLocal i → accumulateDispatch.Preserves i := by decide +kernel +revert

/-- Exactly the contributing parent queries load and add a child value. Selection is proved
from the actual comparisons with digit nine and the current term register. -/
theorem exec_accumulateDispatch {w : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers) (q : ℕ) (hq : x.regs query = q) (hd : x.regs digit = q % 10)
    (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hleft : selected true (x.regs term) q → x.mem (x.regs valueBase + q) = encode a)
    (hright : selected true (x.regs term) q →
      x.mem (x.regs childValues + q / 10) = encode b)
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10)) :
    ∃ y, ExecWithin (w + 2) accumulateDispatch x y 25 ∧
      y.mem = (if selected true (x.regs term) q then
        Function.update x.mem (x.regs valueBase + q) (encode (a + b)) else x.mem) ∧
      (∀ i, ¬AccumulateDispatchLocal i → y.regs i = x.regs i) := by
  by_cases hsel : selected true (x.regs term) q
  · obtain ⟨y, hy, hmem, _⟩ := exec_addValue ha hb x q hq h10 (hleft hsel) (hright hsel) hp hc
    have hchoice : q % 10 = 9 ∨ q % 10 = x.regs term := hsel
    have he : ExecWithin (w + 2) accumulateDispatch x y 25 := by
      by_cases hfirst : q % 10 = 9
      · exact (ExecWithin.branch_pos (by
          simpa only [Cond.holds_eq, hd, h9] using hfirst) hy).mono (by decide)
      · have hsecond := hchoice.resolve_left hfirst
        exact (ExecWithin.branch_neg (by
          simpa only [Cond.holds_eq, hd, h9] using hfirst)
          (ExecWithin.branch_pos (by simpa only [Cond.holds_eq, hd] using hsecond) hy)).mono
            (by decide)
    exact ⟨y, he, by simpa only [hsel, ↓reduceIte] using hmem,
      fun i hi => he.regs_eq (accumulateDispatch_preserves i hi)⟩
  · have hfirst : q % 10 ≠ 9 := fun h => hsel (Or.inl h)
    have hsecond : q % 10 ≠ x.regs term := fun h => hsel (Or.inr h)
    let y := x.set temporary (x.regs temporary)
    have he : ExecWithin (w + 2) accumulateDispatch x y 5 :=
      ExecWithin.branch_neg (by simpa only [Cond.holds_eq, hd, h9] using hfirst)
        (ExecWithin.branch_neg (by simpa only [Cond.holds_eq, hd] using hsecond) ExecWithin.copy)
    exact ⟨y, he.mono (by decide), by simp [hsel, y],
      fun i hi => he.regs_eq (accumulateDispatch_preserves i hi)⟩

/-- Registers changed by loading, dispatching and advancing one parent query. -/
def AccumulateStepLocal (i : Fin registers) : Prop :=
  AccumulateDispatchLocal i ∨ i = query ∨ i = digit ∨ i = index

instance (i : Fin registers) : Decidable (AccumulateStepLocal i) :=
  inferInstanceAs (Decidable
    (AccumulateDispatchLocal i ∨ i = query ∨ i = digit ∨ i = index))

private theorem accumulateStep_preserves (i : Fin registers) :
    ¬AccumulateStepLocal i → accumulateStep.Preserves i := by decide +kernel +revert

/-- One complete native parent-query iteration, including every index/digit/control operation.
The conditional memory hypotheses reflect only which child words are actually requested. -/
theorem exec_accumulateStep {w : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h1 : x.regs one = 1) (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hleft : selected true (x.regs term) q → x.mem (x.regs valueBase + q) = encode a)
    (hright : selected true (x.regs term) q →
      x.mem (x.regs childValues + q / 10) = encode b)
    (h10fit : Fits (w + 2) 10)
    (hr : Fits (w + 2) (x.regs listBase + x.regs index))
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10))
    (hi : Fits (w + 2) (x.regs index + 1)) :
    ∃ y, ExecWithin (w + 2) accumulateStep x y 29 ∧ y.regs index = x.regs index + 1 ∧
      y.mem = (if selected true (x.regs term) q then
        Function.update x.mem (x.regs valueBase + q) (encode (a + b)) else x.mem) ∧
      (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i) := by
  let z := ((x.set address (x.regs listBase + x.regs index)).set query q).set digit (q % 10)
  have hmod : Fits (w + 2) (q % 10) :=
    h10fit.of_le (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  have hload : ExecWithin (w + 2) scanLoad x z 3 := by
    ram_eval [scanLoad, z, hq, h10, hr, hmod, address, listBase, index, query, digit, ten,
      Fin.mk.injEq]
  have hzreg (i : Fin registers) (ha : i ≠ address) (hq' : i ≠ query) (hd : i ≠ digit) :
      z.regs i = x.regs i := by simp [z, ha, hq', hd]
  obtain ⟨u, hu, hm, hf⟩ := exec_accumulateDispatch ha hb z q
    (by simp [z, query, digit]) (by simp [z])
    ((hzreg nine (by decide) (by decide) (by decide)).trans h9)
    ((hzreg ten (by decide) (by decide) (by decide)).trans h10)
    (by simpa +decide [z, term, address, query, digit, valueBase] using hleft)
    (by simpa +decide [z, term, address, query, digit, childValues] using hright)
    (by simpa +decide [z, address, query, digit, valueBase] using hp)
    (by simpa +decide [z, address, query, digit, childValues] using hc)
  have hui : u.regs index = x.regs index :=
    (hf index (by decide)).trans (hzreg index (by decide) (by decide) (by decide))
  have huo : u.regs one = 1 :=
    (hf one (by decide)).trans ((hzreg one (by decide) (by decide) (by decide)).trans h1)
  let y := u.set index (x.regs index + 1)
  have hinc : ExecWithin (w + 2) (ram[ index ← index + one ]) u y 1 := by
    ram_eval [y, hui, huo, hi]
  have he : ExecWithin (w + 2) accumulateStep x y 29 := hload.seq (hu.seq hinc)
  refine ⟨y, he, by simp [y], ?_, fun i hi => he.regs_eq (accumulateStep_preserves i hi)⟩
  simpa +decide [y, z, term, address, query, digit, valueBase] using hm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
