/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountTriple
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CollisionTest

/-!
# Complete native collision queries for Chan–He prime searches

A query computes all three collision counts and tests their scaled thresholds. No count or
acceptance test is supplied as advice: all counting and comparison instructions are charged.

## Main definitions

* `Query.program`: the complete native collision-count and threshold query.

## Main results

* `Query.exec`: exact three-inequality acceptance, input frame and instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Query

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum.ChanHe

/-- Count collisions and test all three inequalities. -/
def program : Code .standard 64 := .seq CountTriple.program CollisionTest.program

/-- Execute a complete three-set collision query within
`34(n₀+n₁+n₂)+15M+85` instructions. Multiplication fits are bounded by `nⱼ²·card`,
independently of the actual input collision count. The final halt is excluded. -/
theorem exec {w M : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs CountCall.modulus = encode (M : ℤ))
    (hfit : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hs : ∀ j, Fits (w + 2) (x.regs (CountCall.source j) + x.regs (CountCall.length j)))
    (hk : ∀ j, Fits (w + 2) (x.regs CountCall.scratch + x.regs (CountCall.length j)))
    (hd : Fits (w + 2) (x.regs CountCall.histogram + M))
    (ht : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) +
      x.regs (CountCall.length j) + 1))
    (hproduct : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) *
      x.regs CollisionTest.card))
    (hz : x.regs CollisionTest.zero = 0)
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        (34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
          x.regs (CountCall.length 2)) + 15 * M + 85) ∧
      y.regs CollisionTest.good = (if
        coll ((Finset.range (x.regs (CountCall.length 0))).image (values 0)) M *
          x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 0) ∧
        coll ((Finset.range (x.regs (CountCall.length 1))).image (values 1)) M *
          x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 1) ∧
        coll ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) M *
          x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 2) then 1 else 0) ∧
      (∀ i, ((28 ≤ i.val ∧ i.val < 37) ∨ 40 ≤ i.val) →
        i ≠ CollisionTest.scaled → i ≠ CollisionTest.good → y.regs i = x.regs i) ∧
      ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a := by
  obtain ⟨a, ha, hav, har, ham⟩ := CountTriple.exec x values hM hmod hmodreg
    hfit hs hk hd ht hsk hkd hinput hinj
  have hac : a.regs CollisionTest.card = x.regs CollisionTest.card := har _ (by decide)
  have hat (j : Fin 3) : a.regs (CollisionTest.threshold j) =
      x.regs (CollisionTest.threshold j) := har _ (by dsimp [CollisionTest.threshold]; omega)
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  have hprod (j : Fin 3) :
      Fits (w + 2) (a.regs (CountCall.result j) * a.regs CollisionTest.card) := by
    rw [hav j, hac]
    apply (hproduct j).of_le
    apply Nat.mul_le_mul_right
    have hcard : ((Finset.range (x.regs (CountCall.length j))).image (values j)).card ≤
        x.regs (CountCall.length j) :=
      Finset.card_image_le.trans_eq (Finset.card_range _)
    exact (coll_le_sq _ _).trans (by simpa only [pow_two] using Nat.mul_self_le_mul_self hcard)
  obtain ⟨b, hb, hbg, hbm, hbr⟩ := CollisionTest.exec a h1
    ((har _ (by decide)).trans hz) hprod
  refine ⟨b, (ha.seq hb).mono (by omega), ?_, ?_, ?_⟩
  · simpa only [hav, hac, hat] using hbg
  · intro i hi hs hg
    exact (hbr i hs hg).trans (har i hi)
  · intro i hi
    rw [hbm]
    exact ham i hi

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Query
