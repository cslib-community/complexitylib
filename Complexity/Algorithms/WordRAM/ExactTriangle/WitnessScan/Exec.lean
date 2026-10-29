/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Cell
public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Setup
public import Complexity.Computability.GenericRAM.Signed.Fits

/-!
# Complete native original-weight interval verification

Every interval vertex is tested by actual charged code. The returned flag characterizes
existence of an original zero sum, and a successful run returns an original-coordinate witness.
Arguments and all memory are preserved. The magnitude and address bounds here are numerical
component premises; the producer/product consumer derives them from its original input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

private theorem args_of_eq (A : Args) {x y : Data 32} (hx : A.InRegisters x)
    (h : ∀ i : Fin 32, 9 ≤ i.val → i.val < 17 → y.regs i = x.regs i) :
    A.InRegisters y := by
  simpa only [Args.InRegisters, h Reg.ab (by decide) (by decide),
    h Reg.bc (by decide) (by decide), h Reg.ac (by decide) (by decide),
    h Reg.size (by decide) (by decide), h Reg.a (by decide) (by decide),
    h Reg.b (by decide) (by decide), h Reg.first (by decide) (by decide),
    h Reg.length (by decide) (by decide)] using hx

private theorem finish_preserves : ∀ i : Fin 32,
    (9 ≤ i.val ∧ i.val < 20) ∨ i = Reg.one ∨ i = Reg.zero →
      finishVertex.Preserves i := by decide

/-- Read and verify the original signed arrays, preserving the argument bank and all memory.
The bound excludes only a final halt. The success flag is raw unsigned 0/1; the witness is an
original vertex, not a middle-label or modular candidate. -/
theorem exec {w U : ℕ} (A : Args) (AB BC AC : ℕ → ℕ → ℤ) (x : Data 32)
    (hx : A.InRegisters x) (ha : A.a < A.n) (hb : A.b < A.n)
    (hc : A.first + A.length ≤ A.n)
    (hmem : ∀ i < A.n, ∀ j < A.n,
      x.mem (A.ab + (i * A.n + j)) = Signed.encode (AB i j) ∧
      x.mem (A.bc + (i * A.n + j)) = Signed.encode (BC i j) ∧
      x.mem (A.ac + (i * A.n + j)) = Signed.encode (AC i j))
    (hmag : ∀ i < A.n, ∀ j < A.n,
      (AB i j).natAbs ≤ U ∧ (BC i j).natAbs ≤ U ∧ (AC i j).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) A.addressBound) :
    ∃ y, ExecWithin (w + 2) program x y (42 * A.length + 17) ∧
      A.InRegisters y ∧ y.mem = x.mem ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔ ∃ c, A.first ≤ c ∧ c < A.first + A.length ∧
        AB A.a A.b + BC A.b c + AC A.a c = 0) ∧
      (y.regs Reg.found = 1 → A.first ≤ y.regs Reg.witness ∧
        y.regs Reg.witness < A.first + A.length ∧
        AB A.a A.b + BC A.b (y.regs Reg.witness) + AC A.a (y.regs Reg.witness) = 0) := by
  let total (c : ℕ) := AB A.a A.b + BC A.b c + AC A.a c
  obtain ⟨s, hs, sargs, smem, sone, szero, sfound, sindex, srowB, srowA, swab⟩ :=
    exec_setup A x (AB A.a A.b) hx ha hb hc (hmem A.a ha A.b hb).1 hfit
  let I (y : Data 32) : Prop := A.InRegisters y ∧ y.mem = x.mem ∧
    y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧
    y.regs Reg.rowB = A.bc + A.b * A.n + A.first ∧
    y.regs Reg.rowA = A.ac + A.a * A.n + A.first ∧
    y.regs Reg.wab = Signed.encode (AB A.a A.b) ∧ y.regs Reg.index ≤ A.length ∧
    (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
    (y.regs Reg.found = 1 ↔ ∃ j < y.regs Reg.index, total (A.first + j) = 0) ∧
    (y.regs Reg.found = 1 → A.first ≤ y.regs Reg.witness ∧
      y.regs Reg.witness < A.first + y.regs Reg.index ∧ total (y.regs Reg.witness) = 0)
  have hstart : I s := by
    refine ⟨sargs, smem, sone, szero, srowB, srowA, swab, by omega,
      Or.inl sfound, ?_, ?_⟩
    · constructor
      · intro h; omega
      · rintro ⟨j, hj, -⟩; omega
    · intro h; omega
  have hrowB : A.b * A.n + A.first ≤ A.n * A.n := by
    have hstep := Nat.mul_le_mul_right A.n (Nat.succ_le_of_lt hb)
    rw [Nat.succ_mul] at hstep
    omega
  have hrowA : A.a * A.n + A.first ≤ A.n * A.n := by
    have hstep := Nat.mul_le_mul_right A.n (Nat.succ_le_of_lt ha)
    rw [Nat.succ_mul] at hstep
    omega
  have hbody (y : Data 32) (hy : I y) (hc' : (Cond.lt Reg.index Reg.length).Holds y) :
      ∃ z, ExecWithin (w + 2) step y z 40 ∧ I z ∧
        A.length - z.regs Reg.index < A.length - y.regs Reg.index := by
    obtain ⟨yargs, ymem, yone, yzero, yrowB, yrowA, ywab, yindex, yflag, yiff, ywit⟩ := hy
    have yl : y.regs Reg.length = A.length := yargs.2.2.2.2.2.2.2
    have hi : y.regs Reg.index < A.length := by
      simpa only [Cond.holds_lt, yl] using hc'
    let i := y.regs Reg.index
    have hcurrent : A.first + i < A.n := by dsimp only [i]; omega
    have hreadB : y.mem (A.bc + A.b * A.n + A.first + i) =
        Signed.encode (BC A.b (A.first + i)) := by
      rw [ymem]
      simpa only [Nat.add_assoc] using (hmem A.b hb (A.first + i) hcurrent).2.1
    have hreadA : y.mem (A.ac + A.a * A.n + A.first + i) =
        Signed.encode (AC A.a (A.first + i)) := by
      rw [ymem]
      simpa only [Nat.add_assoc] using (hmem A.a ha (A.first + i) hcurrent).2.2
    have habmag := (hmag A.a ha A.b hb).1
    have hbcmag := (hmag A.b hb (A.first + i) hcurrent).2.1
    have hacmag := (hmag A.a ha (A.first + i) hcurrent).2.2
    have habfit := hU.of_natAbs_le (habmag.trans (by omega : U ≤ 2 * U))
    have hbcfit := hU.of_natAbs_le (hbcmag.trans (by omega : U ≤ 2 * U))
    have hacfit := hU.of_natAbs_le (hacmag.trans (by omega : U ≤ 2 * U))
    have hsumMag : (AB A.a A.b + BC A.b (A.first + i)).natAbs ≤ 2 * U := by
      have := Int.natAbs_add_le (AB A.a A.b) (BC A.b (A.first + i))
      omega
    have hsumfit := hU.of_natAbs_le hsumMag
    obtain ⟨b, hbtest, bsum, bmem, bmeta⟩ := exec_testVertex y yrowB yrowA rfl ywab
      hreadB hreadA (hfit.of_le (by dsimp only [Args.addressBound]; omega))
      habfit hbcfit hacfit hsumfit
    change b.regs Signed.result = Signed.encode (total (A.first + i)) at bsum
    have bone : b.regs Reg.one = 1 := (bmeta _ (by decide) (by decide)).trans yone
    have bzero : b.regs Reg.zero = 0 := (bmeta _ (by decide) (by decide)).trans yzero
    have bfirst : b.regs Reg.first = A.first :=
      (bmeta _ (by decide) (by decide)).trans yargs.2.2.2.2.2.2.1
    have bindex : b.regs Reg.index = i := bmeta _ (by decide) (by decide)
    have bfound : b.regs Reg.found = y.regs Reg.found := bmeta _ (by decide) (by decide)
    have bwit : b.regs Reg.witness = y.regs Reg.witness := bmeta _ (by decide) (by decide)
    let z := (if total (A.first + i) = 0 then
        b.set Reg.found 1 |>.set Reg.witness (A.first + i)
      else b.set Reg.witness (b.regs Reg.witness)).set Reg.index (i + 1)
    have hfinish : ExecWithin (w + 2) finishVertex b z 4 := by
      have hinc : Fits (w + 2) (i + 1) := hfit.of_le (by
        dsimp only [Args.addressBound]; dsimp only [i]; omega)
      have hpos : Fits (w + 2) (A.first + i) := hfit.of_le (by
        dsimp only [Args.addressBound]; omega)
      by_cases hz : total (A.first + i) = 0
      · have hresult : b.regs Signed.result = 0 := by rw [bsum]; rw [hz]; rfl
        simp only [z, ite_eq_left hz]
        ram_eval [finishVertex, hresult, bone, bzero, bfirst, bindex, hinc, hpos,
          Reg.found, Reg.one, Reg.zero, Reg.witness, Reg.index, Reg.first,
          Signed.result, Fin.mk.injEq]
      · have hresult : b.regs Signed.result ≠ 0 := by
          intro he
          apply hz
          apply Signed.encode_injective
          exact bsum.symm.trans he
        simp only [z, ite_eq_right hz]
        ram_eval [finishVertex, hresult, bone, bzero, bfirst, bindex, hinc,
          Reg.found, Reg.one, Reg.zero, Reg.witness, Reg.index, Reg.first,
          Signed.result, Fin.mk.injEq]
    have zindex : z.regs Reg.index = i + 1 := by simp [z]
    have zflag : z.regs Reg.found = if total (A.first + i) = 0 then 1 else y.regs Reg.found := by
      by_cases hz : total (A.first + i) = 0 <;>
        simp +decide [z, hz, Reg.index, Reg.witness, Reg.found, bfound]
    have zwit : z.regs Reg.witness =
        if total (A.first + i) = 0 then A.first + i else y.regs Reg.witness := by
      by_cases hz : total (A.first + i) = 0 <;>
        simp +decide [z, hz, Reg.index, Reg.witness, bwit]
    have keep (j : Fin 32)
        (hj : (9 ≤ j.val ∧ j.val < 20) ∨ j = Reg.one ∨ j = Reg.zero) :
        z.regs j = y.regs j := by
      have hj9 : 9 ≤ j.val := by
        rcases hj with h | rfl | rfl
        · exact h.1
        · decide
        · decide
      have hjaddr : j ≠ Reg.address := by
        rcases hj with h | rfl | rfl
        · intro he
          have hv := congrArg Fin.val he
          change j.val = 24 at hv
          omega
        · decide
        · decide
      exact (hfinish.regs_eq (finish_preserves j hj)).trans (bmeta j hj9 hjaddr)
    have zmem : z.mem = b.mem := by
      by_cases hz : total (A.first + i) = 0 <;> simp [z, hz]
    refine ⟨z, hbtest.seq hfinish, ?_, ?_⟩
    · refine ⟨args_of_eq A yargs (fun j hj hj' => keep j (Or.inl ⟨hj, by omega⟩)),
        zmem.trans (bmem.trans ymem), (keep _ (Or.inr (Or.inl rfl))).trans yone,
        (keep _ (Or.inr (Or.inr rfl))).trans yzero,
        (keep _ (Or.inl ⟨by decide, by decide⟩)).trans yrowB,
        (keep _ (Or.inl ⟨by decide, by decide⟩)).trans yrowA,
        (keep _ (Or.inl ⟨by decide, by decide⟩)).trans ywab,
        by rw [zindex]; dsimp only [i]; omega, ?_, ?_, ?_⟩
      · rw [zflag]
        split_ifs <;> omega
      · rw [zflag, zindex]
        by_cases hz : total (A.first + i) = 0
        · rw [ite_eq_left hz]
          exact ⟨fun _ => ⟨i, by omega, hz⟩, fun _ => rfl⟩
        · rw [ite_eq_right hz, yiff]
          constructor
          · rintro ⟨j, hj, hzero⟩
            exact ⟨j, by dsimp only [i]; omega, hzero⟩
          · rintro ⟨j, hj, hzero⟩
            refine ⟨j, ?_, hzero⟩
            have hne : j ≠ i := by intro he; subst j; exact hz hzero
            dsimp only [i] at *
            omega
      · intro hfound
        by_cases hz : total (A.first + i) = 0
        · rw [zwit, ite_eq_left hz, zindex]
          exact ⟨by omega, by omega, hz⟩
        · rw [zflag, ite_eq_right hz] at hfound
          obtain ⟨hlo, hhi, hzero⟩ := ywit hfound
          rw [zwit, ite_eq_right hz, zindex]
          exact ⟨hlo, by dsimp only [i]; omega, hzero⟩
    · rw [zindex]
      dsimp only [i]
      omega
  obtain ⟨y, hloop, hy, hdone⟩ := ExecWithin.loop_invariant I
    (fun y => A.length - y.regs Reg.index) hbody hstart
  obtain ⟨yargs, ymem, yone, yzero, yrowB, yrowA, ywab, yindex, yflag, yiff, ywit⟩ := hy
  have ylen : y.regs Reg.length = A.length := yargs.2.2.2.2.2.2.2
  have yend : y.regs Reg.index = A.length := by
    simp only [Cond.holds_lt, ylen] at hdone
    omega
  refine ⟨y, (hs.seq hloop).mono (by rw [sindex]; omega), yargs, ymem, yflag, ?_, ?_⟩
  · constructor
    · intro hfound
      obtain ⟨j, hj, hz⟩ := yiff.mp hfound
      exact ⟨A.first + j, by omega, by rw [yend] at hj; omega, hz⟩
    · rintro ⟨c, hlo, hhi, hz⟩
      apply yiff.mpr
      refine ⟨c - A.first, by rw [yend]; omega, ?_⟩
      simpa only [Nat.add_sub_of_le hlo] using hz
  · intro hfound
    simpa only [yend] using ywit hfound

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
