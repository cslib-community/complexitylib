/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Delivery
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Selection
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Exec

/-!
# Actual selected-prime complete fast execution

The real selector returns a minimum modular-count prime. One actual instruction delivers that
prime to the complete callable solver. Original readback survives the selector's dirty scratch,
and the final workspace frame covers the union of the actual counting and solving intervals.
These are internal staged rules: the whole program computes the parameter postconditions and
derives all numerical fits from original inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem window_le {n d g p q T : ℕ} (h : p ≤ q) :
    CallableFixedPrime.windowSize n d g p T ≤ CallableFixedPrime.windowSize n d g q T := by
  unfold CallableFixedPrime.windowSize CallableFixedPrime.sourceWidth
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _
    (Nat.clog_mono_right 2 (by omega)))

private theorem original_bound {n F : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (q : ℕ) (hq : q < 3 * (n * n)) : (values.getD q 0).natAbs ≤ F := by
  have hq' : q < values.length := by omega
  rw [List.getD_eq_getElem _ _ hq']
  exact hv _ (List.getElem_mem hq')

/-- Concrete selection followed by the complete concrete solver, with both verdict directions.
Parameter postconditions here are established by the real preceding parameter execution; none
is a runtime certificate or a hypothesis about an unspecified algorithm. -/
theorem exec_fast {w W n F b : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hblocks : 0 < ParameterChoice.blocks n)
    (x : Data 640) (xn : x.regs CallableFixedPrime.Reg.n = n)
    (xd : x.regs (parameterBank DyadicParameters.Reg.window) = D (ParameterChoice.level n))
    (xg : x.regs (parameterBank DyadicParameters.Reg.groups) = ParameterChoice.groups n)
    (xb : x.regs CallableFixedPrime.Reg.base = b)
    (hab : x.regs CallableFixedPrime.Reg.ab + n * n ≤ b)
    (hbc : x.regs CallableFixedPrime.Reg.bc + n * n ≤ b)
    (hac : x.regs CallableFixedPrime.Reg.ac + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (x.regs CallableFixedPrime.Reg.ab + q) =
      Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (x.regs CallableFixedPrime.Reg.bc + q) =
      Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (x.regs CallableFixedPrime.Reg.ac + q) =
      Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hmag : GenericRAM.Signed.Fits w (CountPrime.magnitudeBudget
      (Nat.sqrt (D (ParameterChoice.level n))) (Nat.clog 2 n) F : ℤ))
    (haddr : Fits (w + 2) (CountPrime.addressBudget n
      (Nat.sqrt (D (ParameterChoice.level n))) (Nat.clog 2 n) b
      (x.regs CallableFixedPrime.Reg.ab) (x.regs CallableFixedPrime.Reg.bc)
      (x.regs CallableFixedPrime.Reg.ac)))
    (hwidth : w + 2 ≤ W)
    (hctrl : Fits W (4 * (D (ParameterChoice.level n) + 2) *
      (D (ParameterChoice.level n) + 2) + 4))
    (hfit : Fits W (b + 4 * CallableFixedPrime.windowSize n (D (ParameterChoice.level n))
      (ParameterChoice.groups n) (Nat.sqrt (D (ParameterChoice.level n)))
      (CallableFixedPrime.rawTotal n values) + 1024)) :
    let V := fun q => values.getD q 0
    let A := fun i j : Fin n => V (pairIndex (i, j))
    let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
    let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
    let hn : 0 < n := hblocks.trans_le
      ((ParameterChoice.blocks_le_log n).trans (Nat.log_le_self 2 n))
    ∃ (p : ℕ) (a : Data 64), IsSelectedPrime A B C (D (ParameterChoice.level n)) p ∧
      Instances.Output n (D (ParameterChoice.level n)) (ParameterChoice.groups n) p V
        (.init (PreparationInput.input n (D (ParameterChoice.level n))
          (ParameterChoice.groups n) p values)) a ∧
      ∃ y, ExecWithin W fast x y
          (8 + PrimeSelection.timeBound n (D (ParameterChoice.level n)) + 1 +
            CallableFixedPrime.timeBound (m := ParameterChoice.level n) hn
              (ParameterChoice.groups n) p values a.mem) ∧
        (y.regs CallableFixedPrime.Reg.found = 0 ∨ y.regs CallableFixedPrime.Reg.found = 1) ∧
        (y.regs CallableFixedPrime.Reg.found = 1 ↔ HasZeroTriangle A B C) ∧
        y.regs CallableFixedPrime.Reg.scans ≤ falsePositiveCount A B C p +
          y.regs CallableFixedPrime.Reg.found ∧
        (∀ q, q < b ∨ max
          (CountPrime.memoryEnd n (Nat.sqrt (D (ParameterChoice.level n))) (Nat.clog 2 n) b)
          (b + CallableFixedPrime.windowSize n (D (ParameterChoice.level n))
            (ParameterChoice.groups n) (Nat.sqrt (D (ParameterChoice.level n)))
            (CallableFixedPrime.rawTotal n values)) ≤ q → y.mem q = x.mem q) ∧
        ∀ j : Fin 640, (143 ≤ j.val ∧ j.val < 160) ∨ j = CallableFixedPrime.Reg.n ∨
          (604 ≤ j.val ∧ j.val ≤ 607) → y.regs j = x.regs j := by
  have hn : 0 < n := hblocks.trans_le
    ((ParameterChoice.blocks_le_log n).trans (Nat.log_le_self 2 n))
  have hD : 16 ≤ D (ParameterChoice.level n) := ParameterChoice.window_ge_sixteen hblocks
  have hN : D (ParameterChoice.level n) ^ 18 ≤ n := ParameterChoice.geometry hn
  have hg : 1 ≤ ParameterChoice.groups n := ParameterChoice.groups_pos n
  obtain ⟨s, hs, sm, sd, sg, sn, sw, sa, sb, sc, sf, sr⟩ := exec_selectArguments (W := W) x
  obtain ⟨r, hr, hprime, hcount, rframe, rr⟩ := exec_selectPrime s
    (fun q => values.getD q 0) (fun q => values.getD (n * n + q) 0)
    (fun q => values.getD (2 * (n * n) + q) 0)
    hD (sn.trans xn) (sw.trans xd) sa sb sc (sf.trans xb) hab hbc hac
    (fun q hq => original_bound values hlen hv q (by omega))
    (fun q hq => original_bound values hlen hv (n * n + q) (by omega))
    (fun q hq => original_bound values hlen hv (2 * (n * n) + q) (by omega))
    (fun q hq => (congrFun sm _).trans (vab q hq))
    (fun q hq => (congrFun sm _).trans (vbc q hq))
    (fun q hq => (congrFun sm _).trans (vac q hq)) hmag haddr hwidth hctrl
  let p := r.regs (selectorBank PrimeSelection.Reg.best)
  have hp : p ∈ Nat.sqrtPrimeWindow (D (ParameterChoice.level n)) := hprime.1
  have hcap : p ≤ Nat.sqrt (D (ParameterChoice.level n)) := Nat.le_sqrt.mpr
    (by simpa only [pow_two] using (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).2.2.le)
  let q := r.set CallableFixedPrime.Reg.prime p
  have deliver : ExecWithin (B := .standard) W
      (.op (.copy CallableFixedPrime.Reg.prime (selectorBank PrimeSelection.Reg.best))) r q 1 :=
    ExecWithin.copy
  have qkeep (j : Fin 640) (hj : 143 ≤ j.val)
      (hdj : j ≠ CallableFixedPrime.Reg.dimension) (hgj : j ≠ CallableFixedPrime.Reg.groups)
      (hpj : j ≠ CallableFixedPrime.Reg.prime) : q.regs j = x.regs j := by
    exact (Function.update_of_ne hpj _ _).trans ((rr j hj).trans (sr j hj hdj hgj))
  have qn : q.regs CallableFixedPrime.Reg.n = n :=
    (qkeep _ (by decide) (by decide) (by decide) (by decide)).trans xn
  have qd : q.regs CallableFixedPrime.Reg.dimension = D (ParameterChoice.level n) :=
    (Function.update_of_ne (by decide : CallableFixedPrime.Reg.dimension ≠
      CallableFixedPrime.Reg.prime) p r.regs).trans
      ((rr _ (by decide)).trans (sd.trans xd))
  have qg : q.regs CallableFixedPrime.Reg.groups = ParameterChoice.groups n :=
    (Function.update_of_ne (by decide : CallableFixedPrime.Reg.groups ≠
      CallableFixedPrime.Reg.prime) p r.regs).trans
      ((rr _ (by decide)).trans (sg.trans xg))
  have qb : q.regs CallableFixedPrime.Reg.base = b :=
    (qkeep _ (by decide) (by decide) (by decide) (by decide)).trans xb
  have qa : q.regs CallableFixedPrime.Reg.ab = x.regs CallableFixedPrime.Reg.ab :=
    qkeep _ (by decide) (by decide) (by decide) (by decide)
  have qB : q.regs CallableFixedPrime.Reg.bc = x.regs CallableFixedPrime.Reg.bc :=
    qkeep _ (by decide) (by decide) (by decide) (by decide)
  have qc : q.regs CallableFixedPrime.Reg.ac = x.regs CallableFixedPrime.Reg.ac :=
    qkeep _ (by decide) (by decide) (by decide) (by decide)
  have same (u : ℕ) (hu : u < b) : q.mem u = x.mem u :=
    (rframe u (Or.inl hu)).trans (congrFun sm u)
  have hm := window_le (n := n) (d := D (ParameterChoice.level n))
    (g := ParameterChoice.groups n) (T := CallableFixedPrime.rawTotal n values) hcap
  obtain ⟨a, hout, y, hy, yf, ys, yiff, yw, yframe, yr⟩ :=
    CallableFixedPrime.exec_at (m := ParameterChoice.level n) values hlen hD hg hp hN
      q qn qd qg rfl qb (by simpa only [qa] using hab)
      (by simpa only [qB] using hbc) (by simpa only [qc] using hac)
      (fun u hu => by rw [qa]; exact (same _ (by omega)).trans (vab u hu))
      (fun u hu => by rw [qB]; exact (same _ (by omega)).trans (vbc u hu))
      (fun u hu => by rw [qc]; exact (same _ (by omega)).trans (vac u hu))
      (hfit.of_le (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hm) b) 1024))
  have hsolve : ExecWithin W solve r y
      (1 + CallableFixedPrime.timeBound (m := ParameterChoice.level n) hn
        (ParameterChoice.groups n) p values a.mem) := deliver.seq hy
  refine ⟨p, a, hprime, hout, y, ?_, yf, yiff, ys, ?_, ?_⟩
  · exact (hs.seq (hr.seq hsolve)).mono (le_of_eq (by ring))
  · intro u hu
    have hsmall : u < b ∨ b + CallableFixedPrime.windowSize n (D (ParameterChoice.level n))
        (ParameterChoice.groups n) p (CallableFixedPrime.rawTotal n values) ≤ u := by
      rcases hu with hu | hu
      · exact Or.inl hu
      · exact Or.inr ((Nat.add_le_add_left hm b).trans ((le_max_right _ _).trans hu))
    have hcounter : u < b ∨ CountPrime.memoryEnd n (Nat.sqrt (D (ParameterChoice.level n)))
        (Nat.clog 2 n) b ≤ u := hu.elim Or.inl (fun h => Or.inr ((le_max_left _ _).trans h))
    exact (yframe u hsmall).trans ((rframe u hcounter).trans (congrFun sm u))
  · intro j hj
    have hj' : (143 ≤ j.val ∧ j.val < 160) ∨ j.val = 600 ∨
        (604 ≤ j.val ∧ j.val ≤ 607) := by
      rcases hj with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg Fin.val h))
      · exact Or.inr (Or.inr h)
    have h143 : 143 ≤ j.val := by rcases hj' with h | h | h <;> omega
    have hne (i : Fin 640) (hi : 601 ≤ i.val ∧ i.val ≤ 603) : j ≠ i := by
      intro heq
      have hh := congrArg Fin.val heq
      rcases hj' with h | h | h <;> omega
    have hframe : j.val < 160 ∨ (600 ≤ j.val ∧ j.val < 608) := by
      rcases hj' with h | h | h <;> omega
    exact (yr j hframe).trans (qkeep j h143 (hne _ (by decide))
      (hne _ (by decide)) (hne _ (by decide)))

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
