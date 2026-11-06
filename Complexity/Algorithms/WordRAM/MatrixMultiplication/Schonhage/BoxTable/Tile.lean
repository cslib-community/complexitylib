/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.TileChildren
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Values
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Geometry
import Mathlib.Algebra.BigOperators.Fin

/-!
# Complete native compact box-value table

The native e-major loop writes one signed value per computed catalogue record. Its
children have smaller actual compact ranks, so no value-table clearing or assumed
table construction is used. Original encoding-array bounds cover all signed partials.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Finset Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

private theorem exists_count_rank (p : ℕ → Prop) [DecidablePred p] {S j : ℕ}
    (hj : j < Nat.count p S) : ∃ s < S, p s ∧ Nat.count p s = j := by
  induction S with
  | zero => simp at hj
  | succ S ih =>
    by_cases hp : p S
    · rw [Nat.count_succ_eq_succ_count hp] at hj
      by_cases hlt : j < Nat.count p S
      · obtain ⟨s, hs, hps, hr⟩ := ih hlt
        exact ⟨s, by omega, hps, hr⟩
      · exact ⟨S, by omega, hp, by omega⟩
    · rw [Nat.count_succ_eq_count hp] at hj
      obtain ⟨s, hs, hps, hr⟩ := ih hj
      exact ⟨s, by omega, hps, hr⟩

private theorem child_stars {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    recordStars L (childSlot L s d) = recordStars L s - 1 := by
  simpa only [childSlot] using recordStars_slot (recordStars L s - 1)
    (⟨childCode L s d, childCode_lt hv he d⟩ : Fin (10 ^ L))

private theorem slotValue_children {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (a b : Leaf L → ℤ) :
    slotValue a b s = ∑ d : Fin 10, slotValue a b (childSlot L s d) := by
  rw [slotValue, boxValue_eq_sum_childSlots hv he]
  exact sum_congr rfl fun d _ => by rw [slotValue, child_stars hv he]

/-- Registers that may change while constructing one tile's compact values. -/
@[expose] def TileLocal (i : Fin registers) : Prop :=
  RecordLocal i ∨ ProductLocal i ∨ ChildLocal i ∨ i = Reg.current ∨
    i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨ i = Reg.nine ∨ i = Reg.three

instance (i : Fin registers) : Decidable (TileLocal i) :=
  inferInstanceAs (Decidable (RecordLocal i ∨ ProductLocal i ∨ ChildLocal i ∨
    i = Reg.current ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨
    i = Reg.nine ∨ i = Reg.three))

private theorem tile_preserves (i : Fin registers) :
    ¬TileLocal i → tile.Preserves i := by decide +revert

private theorem tileValue_preserves (i : Fin registers) :
    ¬(ProductLocal i ∨ ChildLocal i) → tileValue.Preserves i := by decide +revert

/-- Evaluate one actual descriptor using the stored earlier children or two actual leaf words. -/
theorem exec_tileValue {w L H D V AA BB A B s : ℕ} (x : Data registers)
    (a b : Leaf L → ℤ) (hv : Eligible L H s)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hAA : x.regs Reg.arrayA = AA) (hBB : x.regs Reg.arrayB = BB)
    (hc : x.regs Reg.completion = recordCode L s)
    (he : x.regs Reg.stars = recordStars L s)
    (hT : x.regs Reg.span = 10 ^ L) (hp : x.regs Reg.starPower = recordStride L s)
    (h0 : x.regs Reg.nil = 0) (h9 : x.regs Reg.nine = 9)
    (h1 : x.regs Reg.one = 1) (h10 : x.regs Reg.ten = 10)
    (hleft : x.mem (AA + recordCode L s) = Signed.encode (a (completionAt L s)))
    (hright : x.mem (BB + recordCode L s) = Signed.encode (b (completionAt L s)))
    (hrank : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (D + childSlot L s d) = Nat.count (Eligible L H) (childSlot L s d) + 1)
    (hvalue : 0 < recordStars L s → ∀ d : Fin 10, x.mem
      (V + Nat.count (Eligible L H) (childSlot L s d)) =
        Signed.encode (slotValue a b (childSlot L s d)))
    (hfit : Fits (w + 2)
      (D + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tileValue x y 316 ∧
      y.regs Reg.accumulator = Signed.encode (slotValue a b s) ∧ y.mem = x.mem ∧
      (∀ i, ¬(ProductLocal i ∨ ChildLocal i) → y.regs i = x.regs i) := by
  have hTpos : 0 < 10 ^ L := by positivity
  have hcode : recordCode L s < 10 ^ L := Nat.mod_lt _ hTpos
  have heL : recordStars L s ≤ L := hv.1.trans (population_le _ _)
  have hAB : A * B ≤ 10 ^ L * (A * B) := by
    exact Nat.le_mul_of_pos_left _ hTpos
  by_cases he0 : recordStars L s = 0
  · have ha0 : GenericRAM.Signed.Fits w (a (completionAt L s)) :=
      hsigned.of_natAbs_le ((ha _).trans (by omega))
    have hb0 : GenericRAM.Signed.Fits w (b (completionAt L s)) :=
      hsigned.of_natAbs_le ((hb _).trans (by omega))
    have hp0 : GenericRAM.Signed.Fits w
        (a (completionAt L s) * b (completionAt L s)) := by
      apply hsigned.of_natAbs_le
      rw [Int.natAbs_mul]
      exact (Nat.mul_le_mul (ha _) (hb _)).trans (hAB.trans (by omega))
    obtain ⟨y, hy, hyr, hym, _⟩ := exec_leafProduct ha0 hb0 hp0 x
      (by simpa only [hAA, hc] using hleft) (by simpa only [hBB, hc] using hright)
      (hfit.of_le (by rw [hAA, hc]; omega)) (hfit.of_le (by rw [hBB, hc]; omega))
    have hy' : ExecWithin (w + 2) tileValue x y 316 :=
      (hy.branch_pos (by simp [Cond.holds_eq, he, h0, he0])).mono (by decide)
    refine ⟨y, hy', ?_, hym, fun i hi => hy'.regs_eq (tileValue_preserves i hi)⟩
    simpa only [slotValue, he0, boxValue, starsToP0_slotCube] using hyr
  · have hepos : 0 < recordStars L s := Nat.pos_of_ne_zero he0
    let val (d : ℕ) := slotValue a b (childSlot L s ⟨d % 10, Nat.mod_lt _ (by decide)⟩)
    let rank (d : ℕ) := Nat.count (Eligible L H)
      (childSlot L s ⟨d % 10, Nat.mod_lt _ (by decide)⟩)
    let C := 10 ^ (recordStars L s - 1) * (A * B)
    have hC : 10 * C ≤ 10 ^ L * (A * B) := by
      calc
        _ = 10 ^ (recordStars L s - 1 + 1) * (A * B) := by
          dsimp only [C]
          rw [pow_succ]
          ring
        _ = 10 ^ recordStars L s * (A * B) := by rw [Nat.sub_add_cancel hepos]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) heL)
    let u := (x.set Reg.accumulator 0).set Reg.term 0
    have hf0 : Fits (w + 2) 0 := hfit.of_le (Nat.zero_le _)
    have hstart : ExecWithin (w + 2) childrenStart x u 2 := by
      ram_eval [childrenStart, u, hf0, Reg.accumulator, Reg.term, Fin.mk.injEq]
    have uf (i : Fin registers) (hi : i ≠ Reg.accumulator) (ht : i ≠ Reg.term) :
        u.regs i = x.regs i := by simp [u, hi, ht]
    have hrange (d : ℕ) (hd : d < 10) : rank d ≤ (H + 1) * 10 ^ L := by
      have hslt : childSlot L s ⟨d % 10, Nat.mod_lt _ (by decide)⟩ < (H + 1) * 10 ^ L := by
        have hh := eligible_childSlot hv hepos ⟨d % 10, Nat.mod_lt _ (by decide)⟩
        have hc' := childCode_lt hv hepos ⟨d % 10, Nat.mod_lt _ (by decide)⟩
        have hstar : recordStars L s ≤ H := hv.1.trans hv.2
        dsimp only [childSlot]
        have hm := Nat.mul_le_mul_right (10 ^ L) (show recordStars L s - 1 + 1 ≤ H + 1 by omega)
        rw [Nat.add_one_mul] at hm
        omega
      exact (Nat.count_le _).trans hslt.le
    obtain ⟨y, hy, hyd, hya, hym, _⟩ := exec_childLoop (R := (H + 1) * 10 ^ L) (C := C) u val rank
      ((uf _ (by decide) (by decide)).trans hD) ((uf _ (by decide) (by decide)).trans hV)
      ((uf _ (by decide) (by decide)).trans hc) ((uf _ (by decide) (by decide)).trans he)
      ((uf _ (by decide) (by decide)).trans hT) hTpos
      ((uf _ (by decide) (by decide)).trans hp) (by simp [u])
      (by simp [u, Reg.accumulator, Reg.term])
      ((uf _ (by decide) (by decide)).trans h9) ((uf _ (by decide) (by decide)).trans h1)
      ((uf _ (by decide) (by decide)).trans h10)
      (fun d hd => by
        simpa only [u, Data.set_mem, childSlot, childCode, rank, Nat.mod_eq_of_lt hd]
          using hrank hepos ⟨d, hd⟩)
      (fun d hd => by
        simpa only [u, Data.set_mem, val, rank, Nat.mod_eq_of_lt hd]
          using hvalue hepos (⟨d, hd⟩ : Fin 10)) hrange
      (fun d _ => by
        dsimp only [val, slotValue]
        rw [child_stars hv hepos]
        exact natAbs_boxValue_le a b ha hb _ _)
      (hsigned.of_natAbs_le (by
        simpa only [Int.natAbs_natCast] using hC.trans
          (show 10 ^ L * (A * B) ≤ A + B + 10 ^ L * (A * B) by omega)))
      (hfit.of_le (by
        have hc' := hcode
        have hp' := starStride_le (recordCode L s) (recordStars L s) L
        have heH : recordStars L s ≤ H := hv.1.trans hv.2
        have hes : recordStars L s * 10 ^ L ≤ (H + 1) * 10 ^ L :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [recordStride] at *
        omega))
    have hy' : ExecWithin (w + 2) tileValue x y 316 :=
      ((hstart.seq hy).branch_neg (by simp [Cond.holds_eq, he, h0, he0])).mono (by decide)
    refine ⟨y, hy', ?_, hym, fun i hi => hy'.regs_eq (tileValue_preserves i hi)⟩
    have hsum : (∑ d ∈ range 10, val d) =
        ∑ d : Fin 10, slotValue a b (childSlot L s d) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact sum_congr rfl fun d _ => by simp [val, Nat.mod_eq_of_lt d.isLt]
    rw [slotValue_children hv hepos a b]
    exact hya.trans (congrArg Signed.encode hsum)

/-- Load, evaluate and store one compact record with all native control and address work. -/
theorem exec_tileStep {w L H D R V AA BB A B s : ℕ} (x : Data registers)
    (a b : Leaf L → ℤ) (hv : Eligible L H s) (hs : s < (H + 1) * 10 ^ L)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hj : x.regs Reg.current = Nat.count (Eligible L H) s)
    (hcode : x.mem (R + 3 * Nat.count (Eligible L H) s) = recordCode L s)
    (hstars : x.mem (R + 3 * Nat.count (Eligible L H) s + 1) = recordStars L s)
    (hstride : x.mem (R + 3 * Nat.count (Eligible L H) s + 2) = recordStride L s)
    (hleft : x.mem (AA + recordCode L s) = Signed.encode (a (completionAt L s)))
    (hright : x.mem (BB + recordCode L s) = Signed.encode (b (completionAt L s)))
    (hrank : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (D + childSlot L s d) = Nat.count (Eligible L H) (childSlot L s d) + 1)
    (hvalue : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (V + Nat.count (Eligible L H) (childSlot L s d)) =
        Signed.encode (slotValue a b (childSlot L s d)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tileStep x y 326 ∧
      y.regs Reg.current = Nat.count (Eligible L H) s + 1 ∧
      y.mem = Function.update x.mem (V + Nat.count (Eligible L H) s)
        (Signed.encode (slotValue a b s)) := by
  have hjlt : Nat.count (Eligible L H) s < (H + 1) * 10 ^ L :=
    (Nat.count_le _).trans_lt hs
  obtain ⟨u, hu, uc, ue, up, um, uf⟩ := exec_loadRecord x hx.records hj hx.one hx.three
    (by simpa only [Nat.mul_comm] using hcode)
    (by simpa only [Nat.mul_comm] using hstars)
    (by simpa only [Nat.mul_comm] using hstride) (hfit.of_le (by omega))
  obtain ⟨v, hvexec, vacc, vm, vf⟩ := exec_tileValue u a b hv ha hb
    ((uf _ (by decide)).trans hx.directory) ((uf _ (by decide)).trans hV)
    ((uf _ (by decide)).trans hAA) ((uf _ (by decide)).trans hBB)
    uc ue ((uf _ (by decide)).trans hx.span) up
    ((uf _ (by decide)).trans hx.nil) ((uf _ (by decide)).trans hx.nine)
    ((uf _ (by decide)).trans hx.one) ((uf _ (by decide)).trans hx.ten)
    (by simpa only [um] using hleft) (by simpa only [um] using hright)
    (fun he d => by simpa only [um] using hrank he d)
    (fun he d => by simpa only [um] using hvalue he d)
    (hfit.of_le (by omega)) hsigned
  have vV : v.regs Reg.values = V :=
    (vf _ (by decide)).trans ((uf _ (by decide)).trans hV)
  have vj : v.regs Reg.current = Nat.count (Eligible L H) s :=
    (vf _ (by decide)).trans ((uf _ (by decide)).trans hj)
  have v1 : v.regs Reg.one = 1 :=
    (vf _ (by decide)).trans ((uf _ (by decide)).trans hx.one)
  have haddr : Fits (w + 2) (V + Nat.count (Eligible L H) s) := hfit.of_le (by omega)
  have hinc : Fits (w + 2) (Nat.count (Eligible L H) s + 1) := hfit.of_le (by omega)
  let y := ((v.set Reg.address (V + Nat.count (Eligible L H) s)).write
    (V + Nat.count (Eligible L H) s) (Signed.encode (slotValue a b s))).set
      Reg.current (Nat.count (Eligible L H) s + 1)
  have hstore : ExecWithin (w + 2) tileStore v y 3 := by
    ram_eval [tileStore, y, vV, vj, v1, vacc, haddr, hinc,
      Reg.address, Reg.values, Reg.current, Reg.accumulator, Reg.one, Fin.mk.injEq]
  have hy : ExecWithin (w + 2) tileStep x y 326 := hu.seq (hvexec.seq hstore)
  exact ⟨y, hy, by simp [y], by simp only [y, Data.set_mem, Data.write_mem, vm, um]⟩

/-- The native compact loop computes every eligible slot, preserving the catalogue and inputs. -/
theorem exec_tileLoop {w L H D R V AA BB A B : ℕ} {μ : ℕ → ℕ} (x : Data registers)
    (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hcount : x.regs Reg.count = Nat.count (Eligible L H) ((H + 1) * 10 ^ L))
    (hcurrent : x.regs Reg.current = 0)
    (hcat : CataloguePrefix L H D R ((H + 1) * 10 ^ L) μ x.mem)
    (hDR : D + (H + 1) * 10 ^ L ≤ R)
    (hRV : R + 3 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) ≤ V)
    (hAV : AA + 10 ^ L ≤ V) (hBV : BB + 10 ^ L ≤ V)
    (hleft : ∀ c : Fin (10 ^ L), x.mem (AA + c.val) = Signed.encode (a (leafAt c)))
    (hright : ∀ c : Fin (10 ^ L), x.mem (BB + c.val) = Signed.encode (b (leafAt c)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt Reg.current Reg.count) tileStep) x y
        (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 2) ∧
      (∀ s < (H + 1) * 10 ^ L, Eligible L H s →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + Nat.count (Eligible L H) ((H + 1) * 10 ^ L)) →
        y.mem q = x.mem q) := by
  let S := (H + 1) * 10 ^ L
  let K := Nat.count (Eligible L H) S
  let I (y : Data registers) : Prop :=
    CatalogueParameters L H D R y ∧ y.regs Reg.values = V ∧
      y.regs Reg.arrayA = AA ∧ y.regs Reg.arrayB = BB ∧ y.regs Reg.count = K ∧
      y.regs Reg.current ≤ K ∧
      (∀ s < S, Eligible L H s → Nat.count (Eligible L H) s < y.regs Reg.current →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + y.regs Reg.current) → y.mem q = x.mem q)
  have hi : I x := by
    refine ⟨hx, hV, hAA, hBB, hcount, by simp [hcurrent], ?_, fun _ _ => rfl⟩
    simp only [hcurrent, not_lt_zero, IsEmpty.forall_iff, implies_true]
  have hbody (y : Data registers) (hy : I y)
      (hg : (Cond.lt Reg.current Reg.count).Holds y) :
      ∃ z, ExecWithin (w + 2) tileStep y z 326 ∧ I z ∧
        K - z.regs Reg.current < K - y.regs Reg.current := by
    obtain ⟨yp, yV, yA, yB, yK, yj, yvalues, yframe⟩ := hy
    have hjlt : y.regs Reg.current < K := by
      simpa only [Cond.holds_lt, yK] using hg
    obtain ⟨s, hs, hvs, hsj⟩ := exists_count_rank (Eligible L H) hjlt
    have hlow (q : ℕ) (hq : q < V) : y.mem q = x.mem q := yframe q (by omega)
    have hsK : Nat.count (Eligible L H) s < K := Nat.count_strict_mono hvs hs
    have hrec : R + 3 * Nat.count (Eligible L H) s + 2 < V := by
      dsimp only [K] at hsK
      omega
    have hcode : recordCode L s < 10 ^ L := Nat.mod_lt _ (by positivity)
    obtain ⟨z, hz, hzj, hzm⟩ := exec_tileStep y a b hvs hs ha hb yp yV yA yB hsj.symm
      ((hlow _ (by omega)).trans (hcat.code s hs hvs))
      ((hlow _ (by omega)).trans (hcat.stars s hs hvs))
      ((hlow _ hrec).trans (hcat.stride s hs hvs))
      ((hlow _ (by omega)).trans (hleft ⟨recordCode L s, hcode⟩))
      ((hlow _ (by omega)).trans (hright ⟨recordCode L s, hcode⟩))
      (fun he d => by
        have hchild : childSlot L s d < S := (childSlot_lt hvs he d).trans hs
        rw [hlow _ (by dsimp only [S] at hchild; omega), hcat.directory _ hchild,
          directoryWord, ite_eq_left (eligible_childSlot hvs he d)])
      (fun he d => yvalues _ ((childSlot_lt hvs he d).trans hs)
        (eligible_childSlot hvs he d) ((child_rank_lt hvs he d).trans_eq hsj))
      hfit hsigned
    have zregs (i : Fin registers) (h : tileStep.Preserves i) : z.regs i = y.regs i :=
      hz.regs_eq h
    have zp : CatalogueParameters L H D R z := by
      constructor
      · exact (zregs _ (by decide)).trans yp.levels
      · exact (zregs _ (by decide)).trans yp.height
      · exact (zregs _ (by decide)).trans yp.span
      · exact (zregs _ (by decide)).trans yp.directory
      · exact (zregs _ (by decide)).trans yp.records
      · exact (zregs _ (by decide)).trans yp.slots
      · exact (zregs _ (by decide)).trans yp.one
      · exact (zregs _ (by decide)).trans yp.ten
      · exact (zregs _ (by decide)).trans yp.nine
      · exact (zregs _ (by decide)).trans yp.three
      · exact (zregs _ (by decide)).trans yp.nil
    refine ⟨z, hz, ⟨zp, (zregs _ (by decide)).trans yV,
      (zregs _ (by decide)).trans yA, (zregs _ (by decide)).trans yB,
      (zregs _ (by decide)).trans yK, by omega, ?_, ?_⟩, by omega⟩
    · intro i hi hvi hji
      rw [hzm]
      by_cases hij : Nat.count (Eligible L H) i = Nat.count (Eligible L H) s
      · have his : i = s := Nat.count_injective hvi hvs hij
        subst i
        simp
      · rw [Function.update_of_ne (by omega)]
        exact yvalues i hi hvi (by omega)
    · intro q hq
      rw [hzm, Function.update_of_ne (by omega)]
      exact yframe q (by omega)
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => K - y.regs Reg.current) hbody hi
  obtain ⟨yp, yV, yA, yB, yK, yj, yvalues, yframe⟩ := hIy
  have hdone : y.regs Reg.current = K := by
    simp only [Cond.holds_lt, yK, not_lt] at hstop
    omega
  refine ⟨y, ?_, ?_, ?_⟩
  · simpa only [hcurrent, Nat.sub_zero, K, S, Nat.reduceAdd, Nat.mul_comm] using hy
  · intro s hs hv
    exact yvalues s hs hv ((Nat.count_strict_mono hv hs).trans_eq hdone.symm)
  · simpa only [hdone, K, S] using yframe

/-- Complete one-tile execution, including actual constant/counter setup, with no dirty-memory
restriction. The catalogue and both input arrays lie below the value-table base. -/
theorem exec_tile {w L H D R V AA BB A B : ℕ} {μ : ℕ → ℕ} (x : Data registers)
    (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hcount : x.regs Reg.count = Nat.count (Eligible L H) ((H + 1) * 10 ^ L))
    (hcat : CataloguePrefix L H D R ((H + 1) * 10 ^ L) μ x.mem)
    (hDR : D + (H + 1) * 10 ^ L ≤ R)
    (hRV : R + 3 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) ≤ V)
    (hAV : AA + 10 ^ L ≤ V) (hBV : BB + 10 ^ L ≤ V)
    (hleft : ∀ c : Fin (10 ^ L), x.mem (AA + c.val) = Signed.encode (a (leafAt c)))
    (hright : ∀ c : Fin (10 ^ L), x.mem (BB + c.val) = Signed.encode (b (leafAt c)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tile x y
        (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 8) ∧
      (∀ s < (H + 1) * 10 ^ L, Eligible L H s →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + Nat.count (Eligible L H) ((H + 1) * 10 ^ L)) →
        y.mem q = x.mem q) ∧ (∀ i, ¬TileLocal i → y.regs i = x.regs i) := by
  obtain ⟨u, hu, u0, u1, u10, u9, u3, um, uf⟩ := exec_constants x
    (hfit.of_le (by omega))
  have hf0 : Fits (w + 2) 0 := hfit.of_le (Nat.zero_le _)
  let v := u.set Reg.current 0
  have hv : ExecWithin (B := .standard) (w + 2) (ram[ Reg.current ← #0 ]) u v 1 := by
    ram_eval [v, hf0]
  have vf0 (i : Fin registers) (hi : i ≠ Reg.current) : v.regs i = u.regs i := by
    simp only [v, Data.set_regs, Function.update_of_ne hi]
  have vp : CatalogueParameters L H D R v := by
    constructor
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.levels)
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.height)
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.span)
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.directory)
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.records)
    · exact (vf0 _ (by decide)).trans
        ((uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.slots)
    · exact (vf0 _ (by decide)).trans u1
    · exact (vf0 _ (by decide)).trans u10
    · exact (vf0 _ (by decide)).trans u9
    · exact (vf0 _ (by decide)).trans u3
    · exact (vf0 _ (by decide)).trans u0
  have vf (i : Fin registers) (hi : i ≠ Reg.current) (h0 : i ≠ Reg.nil)
      (h1 : i ≠ Reg.one) (h10 : i ≠ Reg.ten) (h9 : i ≠ Reg.nine) (h3 : i ≠ Reg.three) :
      v.regs i = x.regs i := by
    simpa only [v, Data.set_regs, Function.update_of_ne hi] using uf i h0 h1 h10 h9 h3
  have vm : v.mem = x.mem := um
  obtain ⟨y, hy, hvalues, hframe⟩ := exec_tileLoop v a b ha hb vp
    ((vf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hV)
    ((vf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hAA)
    ((vf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBB)
    ((vf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount)
    (by simp [v]) (by simpa only [vm] using hcat) hDR hRV hAV hBV
    (fun c => by simpa only [vm] using hleft c)
    (fun c => by simpa only [vm] using hright c) hfit hsigned
  have he : ExecWithin (w + 2) tile x y
      (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 8) := by
    exact ((hu.seq hv).seq hy).mono (by omega)
  refine ⟨y, he, hvalues, ?_, fun i hi => he.regs_eq (tile_preserves i hi)⟩
  simpa only [vm] using hframe

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
