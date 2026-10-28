/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Emit
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanSet

/-!
# Charged native suffix selection

## Main results

* `PrunedQuery.exec_suffix`: one real quotient computation and timestamp insertion,
  within ten native instructions, with its complete memory and register frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by shortening a query and attempting its insertion. -/
def SuffixLocal (i : Fin registers) : Prop := EmitLocal i ∨ i = suffix

instance (i : Fin registers) : Decidable (SuffixLocal i) :=
  inferInstanceAs (Decidable (EmitLocal i ∨ i = suffix))

private theorem suffix_preserves (child : Bool) (i : Fin registers) :
    ¬SuffixLocal i → (putSuffix child).Preserves i := by decide +kernel +revert

/-- The selected suffix is divided from the actual loaded query, then deduplicated by its
actual memory timestamp. No query-set computation is supplied as a hypothesis. -/
theorem exec_suffix {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (h1 : x.regs one = 1) (h10 : x.regs ten = 10)
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w (putSuffix child) x y 10 ∧ y.regs suffix = shortened child q ∧
      y.regs childCount =
        (if x.mem (x.regs stamps + shortened child q) = x.regs epoch then
          x.regs childCount else x.regs childCount + 1) ∧
      y.mem =
        (if x.mem (x.regs stamps + shortened child q) = x.regs epoch then x.mem else
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch)) ∧
      (∀ i, ¬SuffixLocal i → y.regs i = x.regs i) := by
  let z := x.set suffix (shortened child q)
  have hqfit : Fits w (shortened child q) := hs.of_le (by omega)
  have hpre : ExecWithin w
      (if child then ram[ suffix ← query / ten ] else ram[ suffix ← query ]) x z 1 := by
    cases child with
    | false =>
      change ExecWithin w (ram[ suffix ← query ]) x z 1
      ram_eval [z, shortened, hq]
    | true =>
      have hv : Fits w (q / 10) := hqfit
      change ExecWithin w (ram[ suffix ← query / ten ]) x (x.set suffix (q / 10)) 1
      ram_eval [hq, h10, hv]
  have hz1 : z.regs one = 1 := by simpa [z, one, suffix] using h1
  have hzs : Fits w (z.regs stamps + z.regs suffix) := by
    simpa [z, stamps, suffix] using hs
  have hzl : Fits w (z.regs childList + z.regs childCount) := by
    simpa [z, childList, childCount, suffix] using hl
  have hzn : Fits w (z.regs childCount + 1) := by
    simpa [z, childCount, suffix] using hn
  obtain ⟨y, hy, hc, hm, hf⟩ := exec_emit z hz1 hzs hzl hzn
  have he : ExecWithin w (putSuffix child) x y 10 := hpre.seq hy
  refine ⟨y, he, ?_, ?_, ?_, fun i hi => he.regs_eq (suffix_preserves child i hi)⟩
  · simpa [z] using hf suffix (by decide)
  · simpa [z, stamps, suffix, childCount, epoch] using hc
  · simpa [z, stamps, suffix, childList, childCount, epoch] using hm

private theorem dispatch_preserves (child : Bool) (i : Fin registers) :
    ¬SuffixLocal i → (scanDispatch child).Preserves i := by decide +kernel +revert

/-- Execute the actual query filter and unique insertion. The numerical selection is proved
from the two real digit comparisons; it is not a supplied child-set certificate. -/
theorem exec_scanDispatch {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (hdigit : x.regs digit = q % 10)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w (scanDispatch child) x y 14 ∧
      y.regs childCount =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          x.regs childCount + 1 else x.regs childCount) ∧
      y.mem =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch) else x.mem) ∧
      (∀ i, ¬SuffixLocal i → y.regs i = x.regs i) := by
  by_cases hsel : selected child (x.regs term) q
  · obtain ⟨y, hy, _, hc, hm, _⟩ := exec_suffix child x q hq h1 h10 hs hl hn
    have he : ExecWithin w (scanDispatch child) x y 14 := by
      cases child with
      | false => exact hy.mono (by decide)
      | true =>
        have hm : q % 10 = 9 ∨ q % 10 = x.regs term := hsel
        by_cases hfirst : q % 10 = 9
        · exact (ExecWithin.branch_pos (by
            simpa only [Cond.holds_eq, hdigit, h9] using hfirst) hy).mono (by decide)
        · have hsecond := hm.resolve_left hfirst
          exact (ExecWithin.branch_neg (by
            simpa only [Cond.holds_eq, hdigit, h9] using hfirst)
            (ExecWithin.branch_pos (by simpa only [Cond.holds_eq, hdigit] using hsecond) hy)).mono
              (by decide)
    refine ⟨y, he, ?_, ?_, fun i hi => he.regs_eq (dispatch_preserves child i hi)⟩
    · by_cases hseen : x.mem (x.regs stamps + shortened child q) = x.regs epoch <;>
        simpa [hsel, hseen] using hc
    · by_cases hseen : x.mem (x.regs stamps + shortened child q) = x.regs epoch <;>
        simpa [hsel, hseen] using hm
  · have hchild : child = true := by
      cases child <;> simp_all [selected]
    subst hchild
    have hfirst : q % 10 ≠ 9 := fun h => hsel (Or.inl h)
    have hsecond : q % 10 ≠ x.regs term := fun h => hsel (Or.inr h)
    let y := x.set temporary (x.regs temporary)
    have he : ExecWithin w (scanDispatch true) x y 5 :=
      ExecWithin.branch_neg (by simpa only [Cond.holds_eq, hdigit, h9] using hfirst)
        (ExecWithin.branch_neg (by simpa only [Cond.holds_eq, hdigit] using hsecond)
          ExecWithin.copy)
    refine ⟨y, he.mono (by decide), ?_, ?_,
      fun i hi => he.regs_eq (dispatch_preserves true i hi)⟩
    · simp [hsel, y, childCount, temporary]
    · simp [hsel, y]

/-- All scan-step scratch registers; caller pointers, counts and the current epoch are kept. -/
def ScanStepLocal (i : Fin registers) : Prop :=
  SuffixLocal i ∨ i = query ∨ i = digit ∨ i = index

instance (i : Fin registers) : Decidable (ScanStepLocal i) :=
  inferInstanceAs (Decidable (SuffixLocal i ∨ i = query ∨ i = digit ∨ i = index))

private theorem scanStep_preserves (child : Bool) (i : Fin registers) :
    ¬ScanStepLocal i → (scanStep child).Preserves i := by decide +kernel +revert

/-- One complete native scan step includes source indexing, the actual load and digit
computation, conditional deduplicated insertion, and the loop-counter increment. -/
theorem exec_scanStep {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (h10fit : Fits w 10) (hread : Fits w (x.regs listBase + x.regs index))
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) (hi : Fits w (x.regs index + 1)) :
    ∃ y, ExecWithin w (scanStep child) x y 18 ∧ y.regs index = x.regs index + 1 ∧
      y.regs childCount =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          x.regs childCount + 1 else x.regs childCount) ∧
      y.mem =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch) else x.mem) ∧
      (∀ i, ¬ScanStepLocal i → y.regs i = x.regs i) := by
  let z := ((x.set address (x.regs listBase + x.regs index)).set query q).set digit (q % 10)
  have hmod : Fits w (q % 10) := h10fit.of_le (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  have hload : ExecWithin w scanLoad x z 3 := by
    ram_eval [scanLoad, z, hq, h10, hread, hmod, address, listBase, index, query, digit, ten,
      Fin.mk.injEq]
  have hreg (i : Fin registers) (ha : i ≠ address) (hq' : i ≠ query) (hd : i ≠ digit) :
      z.regs i = x.regs i := by simp [z, ha, hq', hd]
  obtain ⟨u, hu, hc, hm, hf⟩ := exec_scanDispatch child z q
    (by simp [z, query, digit]) (by simp [z])
    ((hreg one (by decide) (by decide) (by decide)).trans h1)
    ((hreg ten (by decide) (by decide) (by decide)).trans h10)
    ((hreg nine (by decide) (by decide) (by decide)).trans h9)
    (by simpa [z, stamps, address, query, digit] using hs)
    (by simpa [z, childList, childCount, address, query, digit] using hl)
    (by simpa [z, childCount, address, query, digit] using hn)
  have hui : u.regs index = x.regs index :=
    (hf index (by decide)).trans (hreg index (by decide) (by decide) (by decide))
  have huo : u.regs one = 1 :=
    (hf one (by decide)).trans ((hreg one (by decide) (by decide) (by decide)).trans h1)
  let y := u.set index (x.regs index + 1)
  have hinc : ExecWithin w (ram[ index ← index + one ]) u y 1 := by
    ram_eval [y, hui, huo, hi]
  have he : ExecWithin w (scanStep child) x y 18 := hload.seq (hu.seq hinc)
  refine ⟨y, he, by simp [y], ?_, ?_,
    fun i hi => he.regs_eq (scanStep_preserves child i hi)⟩
  · simpa [y, z, index, childCount, term, address, query, digit, stamps, epoch] using hc
  · simpa [y, z, childList, childCount, term, address, query, digit, stamps, epoch] using hm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
