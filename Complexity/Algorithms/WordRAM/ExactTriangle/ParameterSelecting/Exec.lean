/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Time
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Header

/-!
# Complete parameter-selecting native caller execution

Only original n,F,pointers/workspace and the actual original signed array words are premises.
The real parameter program determines the regime, the real selector determines its prime,
and the real concrete solver or exhaustive block determines the verdict. Both verdict
directions and original-argument/memory frames are established in the same actual final state.
General arbitrary-old-data execution does not assert physical bounds on unused old words;
original-admission prefix theorems impose those resource hypotheses separately.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Actual complete ET caller on original arrays. The selected prime and source-reference
memory are derived witnesses of real calls, never algorithm inputs or assumed contracts. -/
theorem exec_at {W n F ap bp cp b : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (x : Data 640) (xn : x.regs Reg.side = n) (xF : x.regs Reg.bound = F)
    (xap : x.regs Reg.ab = ap) (xbp : x.regs Reg.bc = bp)
    (xcp : x.regs Reg.ac = cp) (xb : x.regs Reg.free = b)
    (hab : ap + n * n ≤ b) (hbc : bp + n * n ≤ b) (hac : cp + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (ap + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (bp + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (cp + q) = Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hW : executionWidth n F b ap bp cp values ≤ W) :
    let V := fun q => values.getD q 0
    let A := fun i j : Fin n => V (pairIndex (i, j))
    let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
    let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
    ∃ (p : ℕ) (mem : ℕ → ℕ) (y : Data 640),
      ExecWithin W program x y (timeBound n p values mem) ∧
      (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
      (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
      (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
      (¬0 < ParameterChoice.blocks n → p = 0) ∧
      (∀ q, q < b ∨ workspaceEnd n b values ≤ q → y.mem q = x.mem q) ∧
      y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = ap ∧
      y.regs Reg.bc = bp ∧ y.regs Reg.ac = cp ∧ y.regs Reg.free = b := by
  let V := fun q => values.getD q 0
  let A := fun i j : Fin n => V (pairIndex (i, j))
  let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
  let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
  obtain ⟨s, hs, sm, sF, sn, sa, sb, sc, sf, spn, sp, _⟩ := exec_save x
    ((envelope_fits values hW).of_le (Nat.zero_le _))
  obtain ⟨a, ha, an, ablocks, al, ad, ag, aL, aflag, am, ar⟩ := exec_parameters s
    (spn.trans xn) (parameter_fits values hW)
  have original (j : Fin 640) (hj : j.val < 144 ∨ 160 ≤ j.val) : a.regs j = s.regs j := ar j hj
  have aF : a.regs Reg.savedBound = F := (original _ (Or.inl (by decide))).trans (sF.trans xF)
  have aN : a.regs CallableFixedPrime.Reg.n = n :=
    (original _ (Or.inr (by decide))).trans (sn.trans xn)
  have aAB : a.regs CallableFixedPrime.Reg.ab = ap :=
    (original _ (Or.inr (by decide))).trans (sa.trans xap)
  have aBC : a.regs CallableFixedPrime.Reg.bc = bp :=
    (original _ (Or.inr (by decide))).trans (sb.trans xbp)
  have aAC : a.regs CallableFixedPrime.Reg.ac = cp :=
    (original _ (Or.inr (by decide))).trans (sc.trans xcp)
  have aBase : a.regs CallableFixedPrime.Reg.base = b :=
    (original _ (Or.inr (by decide))).trans (sf.trans xb)
  have aPrime : a.regs CallableFixedPrime.Reg.prime = 0 :=
    (original _ (Or.inr (by decide))).trans sp
  have aMem : a.mem = x.mem := am.trans sm
  let cond := Cond.lt CallableFixedPrime.Reg.prime (parameterBank DyadicParameters.Reg.fast)
  have finish (p : ℕ) (mem : ℕ → ℕ) (r : Data 640)
      (he : ExecWithin W (.branch cond fast slow) a r (stageBudget n p values mem + 2))
      (hbool : r.regs CallableFixedPrime.Reg.found = 0 ∨ r.regs CallableFixedPrime.Reg.found = 1)
      (hiff : r.regs CallableFixedPrime.Reg.found = 1 ↔ HasZeroTriangle A B C)
      (hprime : 0 < ParameterChoice.blocks n →
        IsSelectedPrime A B C (ParameterChoice.window n) p)
      (hzero : ¬0 < ParameterChoice.blocks n → p = 0)
      (hframe : ∀ q, q < b ∨ workspaceEnd n b values ≤ q → r.mem q = a.mem q)
      (hregs : ∀ j : Fin 640, (143 ≤ j.val ∧ j.val < 160) ∨
        j = CallableFixedPrime.Reg.n ∨ (604 ≤ j.val ∧ j.val ≤ 607) → r.regs j = a.regs j) :
      ∃ y, ExecWithin W program x y (timeBound n p values mem) ∧
        (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
        (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
        (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
        (¬0 < ParameterChoice.blocks n → p = 0) ∧
        (∀ q, q < b ∨ workspaceEnd n b values ≤ q → y.mem q = x.mem q) ∧
        y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = ap ∧
        y.regs Reg.bc = bp ∧ y.regs Reg.ac = cp ∧ y.regs Reg.free = b := by
    obtain ⟨y, hy, ym, yn, yF, ya, yb, yc, yf, yo, _⟩ := exec_restore (W := W) r
    refine ⟨y, hs.seq (ha.seq (he.seq hy)), ?_, ?_, hprime, hzero, ?_,
      yn.trans ((hregs _ (Or.inr (Or.inl rfl))).trans aN),
      yF.trans ((hregs _ (Or.inl ⟨by decide, by decide⟩)).trans aF),
      ya.trans ((hregs _ (Or.inr (Or.inr ⟨by decide, by decide⟩))).trans aAB),
      yb.trans ((hregs _ (Or.inr (Or.inr ⟨by decide, by decide⟩))).trans aBC),
      yc.trans ((hregs _ (Or.inr (Or.inr ⟨by decide, by decide⟩))).trans aAC),
      yf.trans ((hregs _ (Or.inr (Or.inr ⟨by decide, by decide⟩))).trans aBase)⟩
    · simpa only [yo] using hbool
    · simpa only [yo] using hiff
    · intro q hq
      exact (congrFun ym q).trans ((hframe q hq).trans (congrFun aMem q))
  by_cases hfast : 0 < ParameterChoice.blocks n
  · obtain ⟨p, reference, hp, hout, r, hr, rf, riff, rs, frame, regs⟩ := exec_fast values hlen hv
      hfast a aN ad ag aBase (by simpa only [aAB] using hab)
      (by simpa only [aBC] using hbc) (by simpa only [aAC] using hac)
      (fun q hq => by rw [aAB, aMem]; exact vab q hq)
      (fun q hq => by rw [aBC, aMem]; exact vbc q hq)
      (fun q hq => by rw [aAC, aMem]; exact vac q hq)
      (counter_magnitude_fits (n := n) (F := F) (b := b) (ap := ap) (bp := bp) (cp := cp) values)
      (by simpa only [aAB, aBC, aAC, ParameterChoice.window,
        Cslib.Algorithms.MatrixMultiplication.Schonhage.D] using
        counter_address_fits (n := n) (F := F) (b := b) (ap := ap) (bp := bp) (cp := cp) values)
      (by simpa only [executionWidth, Nat.add_assoc] using hW)
      (controller_fits values hW) (callable_fits values hW)
    have hc : cond.Holds a := by
      simpa only [cond, Cond.holds_lt, aPrime, aflag, ite_eq_left hfast] using
        (by decide : 0 < (1 : ℕ))
    have hstage : ExecWithin W fast a r (stageBudget n p values reference.mem) := by
      simpa only [stageBudget, dite_eq_left hfast, ParameterChoice.window,
        Cslib.Algorithms.MatrixMultiplication.Schonhage.D] using hr
    have hbranch : ExecWithin W (.branch cond fast slow) a r
        (stageBudget n p values reference.mem + 2) :=
      (ExecWithin.branch_pos hc hstage).mono (by omega)
    obtain ⟨y, he, yf, yiff, yp, yz, ym, yn, yF, ya, yb, yc, yfree⟩ :=
      finish p reference.mem r hbranch rf riff (fun _ => hp)
        (fun h => False.elim (h hfast)) frame regs
    exact ⟨p, reference.mem, y, he, yf, yiff, yp, yz, ym, yn, yF, ya, yb, yc, yfree⟩
  · have hcell (i j : Fin n) : pairIndex (i, j) < n * n := by
      simpa only [pairIndex, Fin.coe_mkDivMod, Nat.mul_comm] using (Fin.mkDivMod i j).isLt
    have value_bound (q : ℕ) (hq : q < 3 * (n * n)) : (V q).natAbs ≤ F := by
      have hq' : q < values.length := by omega
      dsimp only [V]
      rw [List.getD_eq_getElem _ _ hq']
      exact hv _ (List.getElem_mem hq')
    have abs_bound (q : ℕ) (hq : q < 3 * (n * n)) : |V q| ≤ (F : ℤ) := by
      have hcast : ((V q).natAbs : ℤ) ≤ (F : ℤ) := by exact_mod_cast value_bound q hq
      simpa only [Int.natCast_natAbs] using hcast
    obtain ⟨r, hr, rf, riff, rm, regs⟩ := exec_slow a A B C aN
      (by simpa only [aAB] using hab) (by simpa only [aBC] using hbc)
      (by simpa only [aAC] using hac) (slow_fits values hW)
      (fun i j => by
        rw [aAB, aMem]
        simpa only [A, V, pairIndex, Nat.add_assoc] using vab _ (hcell i j))
      (fun i j => by
        rw [aBC, aMem]
        simpa only [B, V, pairIndex, Nat.add_assoc] using vbc _ (hcell i j))
      (fun i j => by
        rw [aAC, aMem]
        simpa only [C, V, pairIndex, Nat.add_assoc] using vac _ (hcell i j))
      (fun i j => abs_bound _ (by have := hcell i j; omega))
      (fun i j => abs_bound _ (by have := hcell i j; omega))
      (fun i j => abs_bound _ (by have := hcell i j; omega))
    have hc : ¬cond.Holds a := by
      simp only [cond, Cond.holds_lt, aPrime, aflag, ite_eq_right hfast,
        lt_self_iff_false, not_false_eq_true]
    have hstage : ExecWithin W slow a r (stageBudget n 0 values (fun _ => 0)) := by
      simpa only [stageBudget, dite_eq_right hfast] using hr
    have hbranch : ExecWithin W (.branch cond fast slow) a r
        (stageBudget n 0 values (fun _ => 0) + 2) := ExecWithin.branch_neg hc hstage
    have hkeep (j : Fin 640) (hj : (143 ≤ j.val ∧ j.val < 160) ∨
        j = CallableFixedPrime.Reg.n ∨ (604 ≤ j.val ∧ j.val ≤ 607)) : r.regs j = a.regs j := by
      have cases : (143 ≤ j.val ∧ j.val < 160) ∨ j.val = 600 ∨
          (604 ≤ j.val ∧ j.val ≤ 607) := by
        rcases hj with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (congrArg Fin.val h))
        · exact Or.inr (Or.inr h)
      apply regs j
      · rcases cases with h | h | h <;> omega
      · intro h
        have hh : j.val = 632 := congrArg Fin.val h
        rcases cases with h | h | h <;> omega
    obtain ⟨y, he, yf, yiff, yp, yz, ym, yn, yF, ya, yb, yc, yfree⟩ :=
      finish 0 (fun _ => 0) r hbranch (by omega) riff
        (fun h => False.elim (hfast h)) (fun _ => rfl)
        (fun q _ => congrFun rm q) hkeep
    exact ⟨0, (fun _ => 0), y, he, yf, yiff, yp, yz, ym, yn, yF, ya, yb, yc, yfree⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
