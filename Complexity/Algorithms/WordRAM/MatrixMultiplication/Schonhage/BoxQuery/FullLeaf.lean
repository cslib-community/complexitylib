/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Leaf
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.CompleteLeaf
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Memory

/-!
# Original signed meaning of a completed native task

The reached prefix supplies its actual original leaf code and canonical box key.
Source and table readback discharge both native branches. All arithmetic fits follow
from one original magnitude envelope, including zero opposite operands and cancellation.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Consume one actual completed task and add exactly its original finite query value. -/
theorem exec_fullLeaf {w L m t D V AA BB K F A B : ℕ} (x : Data registers)
    (η : OutStr L) (hη : (innerSetO η).card = m) (xs : List Term)
    (hgood : Good η t xs) (hlen : xs.length = L) (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hp : Parameters L t (PrunedQuery.queryIndex η).val AA BB D V K F x)
    (hc : x.regs Reg.code = prefixCode xs) (hu : x.regs Reg.used = usedFrom η 0 xs)
    (hs : x.regs Reg.stars = starsFrom η 0 xs)
    (hr : Readback m t D V AA BB a b x.mem) (z : ℤ)
    (hz : x.regs Reg.answer = Signed.encode z) (hzn : z.natAbs ≤ magnitudeBound L A B)
    (hfit : Fits (w + 2) (D + V + AA + BB + 2 * ((L + 1) * 10 ^ L) + 32))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) leaf x y 39 ∧
      y.regs Reg.answer = Signed.encode
        (z + leafQueryValue m t η a b (completeLeaf xs hlen)) ∧ y.mem = x.mem ∧
      (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  let τ := completeLeaf xs hlen
  let c := prefixCode xs
  let e := starsFrom η 0 xs
  let s := e * 10 ^ L + c
  have hT : 1 ≤ 10 ^ L := Nat.one_le_pow L _ (by decide)
  have he : e ≤ L := by simpa only [e, hlen] using starsFrom_le η 0 xs
  have hcode : c < 10 ^ L := by simpa only [c, hlen] using prefixCode_lt xs
  have hcap : (L + 1) * 10 ^ L = L * 10 ^ L + 10 ^ L := by ring
  have hAB : A * B ≤ 10 ^ (2 * L) * (A * B) := Nat.le_mul_of_pos_left _ (by positivity)
  have hterm : 10 ^ L * (A * B) ≤ 10 ^ (2 * L) * (A * B) := by
    apply Nat.mul_le_mul_right
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hfa : GenericRAM.Signed.Fits w (a τ) :=
    hmag.of_natAbs_le ((ha _).trans (by unfold magnitudeBound; omega))
  have hfb : GenericRAM.Signed.Fits w (b τ) :=
    hmag.of_natAbs_le ((hb _).trans (by unfold magnitudeBound; omega))
  have hfab : GenericRAM.Signed.Fits w (a τ * b τ) := by
    apply hmag.of_natAbs_le
    rw [Int.natAbs_mul]
    exact (Nat.mul_le_mul (ha _) (hb _)).trans (by unfold magnitudeBound; omega)
  have hfz : GenericRAM.Signed.Fits w z := hmag.of_natAbs_le hzn
  have hleft : x.mem (AA + c) = Signed.encode (a τ) := by
    have h := hr.left ⟨c, hcode⟩
    simpa only [c, leafAt_prefixCode xs hlen, τ] using h
  have hright : x.mem (BB + c) = Signed.encode (b τ) := by
    have h := hr.right ⟨c, hcode⟩
    simpa only [c, leafAt_prefixCode xs hlen, τ] using h
  by_cases hd : usedFrom η 0 xs < t
  · obtain ⟨y, hy, hyv, hym, hyf⟩ := exec_leaf (T := 10 ^ L) (c := c) (e := e)
      (d := usedFrom η 0 xs) (t := t) (r := 0) (v := 0) x hfa hfb hfab
      (GenericRAM.Signed.fits_zero hmag.1) hfz hp.directory hp.values hp.arrayA hp.arrayB
      hp.span hc hs hu hp.threshold hp.one hz (fun _ => ⟨hleft, hright⟩)
      (by intro hn; exact False.elim (hn hd))
      (hfit.of_le (by
        have heT := Nat.mul_le_mul_right (10 ^ L) he
        dsimp only [c, e]
        dsimp only [c, e] at hcode heT
        omega))
    refine ⟨y, hy, ?_, hym, hyf⟩
    simpa only [hd, ite_true, completeLeaf_value hgood hlen hη a b, τ] using hyv
  · have ht : usedFrom η 0 xs = t := by have := hgood.2.2; omega
    have heligible := completeLeaf_threshold_eligible hgood hlen hη ht
    have hslot := completeLeaf_threshold_key_lt hgood hlen hη ht
    let r := Nat.count (BoxTable.Eligible L (m - t)) s
    have hrank : x.mem (D + s) = r + 1 := by
      rw [hr.directory s hslot, BoxTable.directoryWord, ite_eq_left heligible]
    have hvalue : x.mem (V + r) = Signed.encode (BoxTable.slotValue a b s) :=
      hr.values s hslot heligible
    have hrS : r < 10 ^ L * (L + 1) := by
      have hm : m ≤ L := by
        have hcard := Finset.card_le_univ (innerSetO η)
        simpa only [hη, Fintype.card_fin] using hcard
      have hr' := (Nat.count_le (BoxTable.Eligible L (m - t)) (n := s)).trans_lt hslot
      have hSL := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
      exact hr'.trans_le (by simpa only [Nat.mul_comm] using hSL)
    rw [Nat.mul_comm] at hrS
    have hfv : GenericRAM.Signed.Fits w (BoxTable.slotValue a b s) :=
      hmag.of_natAbs_le ((BoxTable.natAbs_slotValue_le a b ha hb heligible).trans
        (by unfold magnitudeBound; omega))
    obtain ⟨y, hy, hyv, hym, hyf⟩ := exec_leaf (T := 10 ^ L) (c := c) (e := e)
      (d := usedFrom η 0 xs) (t := t) (r := r) x hfa hfb hfab hfv hfz
      hp.directory hp.values hp.arrayA hp.arrayB hp.span hc hs hu hp.threshold hp.one hz
      (by intro hl; exact False.elim (hd hl)) (fun _ => ⟨hrank, hvalue⟩)
      (hfit.of_le (by
        have heT := Nat.mul_le_mul_right (10 ^ L) he
        dsimp only [c, e]
        dsimp only [c, e] at hcode heT
        omega))
    refine ⟨y, hy, ?_, hym, hyf⟩
    simpa only [completeLeaf_value hgood hlen hη a b, hd, ite_false, τ, s, c, e] using hyv

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
