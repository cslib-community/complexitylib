/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Adapt
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Admission
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Receive

/-!
# Complete caller-safe fixed-prime solver execution

Only runtime original scalars, canonical signed arrays and caller workspace are inputs. The
program copies those arrays once, computes its width, runs the real one-time producer and
all-record solver, and returns its actual original-coordinate witness. The proof's reference
prepared state is an output of the derivation, never a layout/run/time certificate supplied
by the caller. Raw old-word bounds include dirty words before any normalization.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All adaptation, computed modulus, translated source and five return copies, before halt.
The reference memory only indexes existing finite charges; it is not an algorithm input. -/
@[expose] noncomputable def timeBound {m n : ℕ} (hn : 0 < n) (g p : ℕ)
    (values : List ℤ) (mem : ℕ → ℕ) : ℕ :=
  24 * (n * n) + 24669 * Nat.clog 2 (n + D m + g + p + rawTotal n values + 4) + 482 +
    3 * FixedPrime.timeBound (m := m) hn g p values mem

/-- Complete actual native caller execution in the existing unrestricted-data semantics.
No initial whole-data bound is needed to establish execution and semantic/frame guarantees.
Original-word fits are still necessary for physical-word/prefix bounds: use `exec` or the
original-admission prefix rules for those claims. No source run or solver contract is assumed. -/
theorem exec_at {W m n g p b : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (x : Data 640) (xn : x.regs Reg.n = n) (xD : x.regs Reg.dimension = D m)
    (xg : x.regs Reg.groups = g) (xp : x.regs Reg.prime = p) (xb : x.regs Reg.base = b)
    (hab : x.regs Reg.ab + n * n ≤ b) (hbc : x.regs Reg.bc + n * n ≤ b)
    (hac : x.regs Reg.ac + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (x.regs Reg.ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (x.regs Reg.bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (x.regs Reg.ac + q) =
      Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hfit : Fits W (b + 4 * windowSize n (D m) g p (rawTotal n values) + 1024)) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u v : Fin n => V (n * n + pairIndex (u, v))
    let wAC := fun u v : Fin n => V (2 * (n * n) + pairIndex (u, v))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin W program x y (timeBound (m := m) hn g p values a.mem) ∧
        (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs Reg.found = 1 →
          y.regs Reg.witnessA < n ∧ y.regs Reg.witnessB < n ∧ y.regs Reg.witnessC < n ∧
          V (y.regs Reg.witnessA * n + y.regs Reg.witnessB) +
            V (n * n + (y.regs Reg.witnessB * n + y.regs Reg.witnessC)) +
            V (2 * (n * n) + (y.regs Reg.witnessA * n + y.regs Reg.witnessC)) = 0) ∧
        (∀ q, q < b ∨ b + windowSize n (D m) g p (rawTotal n values) ≤ q →
          y.mem q = x.mem q) ∧
        ∀ j : Fin 640, j.val < 160 ∨ (600 ≤ j.val ∧ j.val < 608) → y.regs j = x.regs j := by
  let T := rawTotal n values
  have fit : Fits W (b + 4 * windowSize n (D m) g p T + 1024) := hfit
  have window_fit : Fits W (b + windowSize n (D m) g p T) := fit.of_le (by omega)
  obtain ⟨hw, hS, -, -⟩ := setup_fits fit
  have hT : T ≤ windowSize n (D m) g p T := by omega
  have hI : 5 + 3 * (n * n) ≤ windowSize n (D m) g p T :=
    inputEnd_le_window (m := m) (g := g) (p := p) values hlen
  have hsum : matrixWordSum x.mem n (x.regs Reg.ab) (x.regs Reg.bc) (x.regs Reg.ac) = T :=
    matrixWordSum_eq_rawTotal x.mem values vab vbc vac
  obtain ⟨a, ha, amem, atotal, ameta⟩ := exec_adapt x
    (by simpa only [xn, xb] using hab) (by simpa only [xn, xb] using hbc)
    (by simpa only [xn, xb] using hac)
    (by rw [xn, xb, hsum]; exact fit.of_le (by omega))
  have ha' : ExecWithin W adapt x a (24 * (n * n) + 38) := by simpa only [xn] using ha
  have an : a.regs Reg.n = n := (ameta _ (by decide)).trans xn
  have aD : a.regs Reg.dimension = D m := (ameta _ (by decide)).trans xD
  have ag : a.regs Reg.groups = g := (ameta _ (by decide)).trans xg
  have ap : a.regs Reg.prime = p := (ameta _ (by decide)).trans xp
  have ab : a.regs Reg.base = b := (ameta _ (by decide)).trans xb
  have asum : a.regs Reg.total = T := by simpa only [xn, hsum] using atotal
  have ai (q : ℕ) (hq : q < 5 + 3 * (n * n)) : a.mem (b + q) =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q := by
    rw [amem, xn, xD, xg, xp, xb]
    exact copyMemory_input x.mem values hlen hab hbc hac vab vbc vac q hq
  have af (q : ℕ) (hq : q < b ∨ b + windowSize n (D m) g p T ≤ q) : a.mem q = x.mem q := by
    rw [amem, xn, xD, xg, xp, xb]
    exact copyMemory_outside _ _ _ _ _ _ _ _ _ _ (by omega)
  obtain ⟨s, hs, smem, sb, sM, sr, -⟩ := exec_setup a
    (by simpa only [an, aD, ag, ap, asum, ab] using fit)
  have hs' : ExecWithin W setup a s
      (24669 * Nat.clog 2 (n + D m + g + p + T + 4) + 439) := by
    simpa only [an, aD, ag, ap, asum] using hs
  have sb' : s.regs (sourceBank MemoryWindow.Reg.base) = b := sb.trans ab
  have sM' : s.regs (sourceBank MemoryWindow.Reg.modulus) = windowSize n (D m) g p T := by
    simpa only [an, aD, ag, ap, asum] using sM
  have sr' (i : Fin 416) : Fits (sourceWidth n (D m) g p T) (s.regs (sourceReg i)) := by
    simpa only [an, aD, ag, ap, asum] using sr i
  have si (q : ℕ) (hq : q < 5 + 3 * (n * n)) : s.mem (b + q) =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q := by
    rw [smem]; exact ai q hq
  obtain ⟨reference, hout, z, hz, zf, zs, ziff, zw, zframe⟩ := exec_compiled values hlen
    hD hg hp hN (natAbs_le_rawTotal values hlen) (s.comap sourceBank) sb' sM' sr' si hw window_fit
  let z' := z.extend sourceBank s
  have hsolve : ExecWithin W solve s z'
      (3 * FixedPrime.timeBound (m := m)
        (lt_of_lt_of_le (by omega : 0 < D m)
          ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN))
        g p values reference.mem) := hz.rename sourceBank_injective
  obtain ⟨y, hy, ymem, yf, ya, yb, yc, ys⟩ := exec_receive (W := W) z'
  have zreg (i : Fin 416) : z'.regs (sourceReg i) = z.regs (i.castAdd 3) :=
    sourceBank_injective.extend_apply _ _ _
  have yF : y.regs Reg.found = z.regs (FixedPrime.Reg.found.castAdd 3) := yf.trans (zreg _)
  have yA : y.regs Reg.witnessA =
      z.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessA).castAdd 3) := ya.trans (zreg _)
  have yB : y.regs Reg.witnessB =
      z.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessB).castAdd 3) := yb.trans (zreg _)
  have yC : y.regs Reg.witnessC =
      z.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessC).castAdd 3) := yc.trans (zreg _)
  have yS : y.regs Reg.scans = z.regs (FixedPrime.Reg.scans.castAdd 3) := ys.trans (zreg _)
  have he : ExecWithin W program x y
      (timeBound (m := m)
        (lt_of_lt_of_le (by omega : 0 < D m)
          ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN))
        g p values reference.mem) := by
    apply (ha'.seq (hs'.seq (hsolve.seq hy))).mono
    dsimp only [timeBound, T]
    exact le_of_eq (by ring)
  refine ⟨reference, hout, y, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [yF] using zf
  · simpa only [yS, yF] using zs
  · simpa only [yF] using ziff
  · simpa only [yF, yA, yB, yC] using zw
  · intro q hq
    have hf : z'.mem q = s.mem q := zframe q hq
    exact (congrFun ymem q).trans (hf.trans ((congrFun smem q).trans (af q hq)))
  · intro j hj
    exact he.regs_eq (program_preserves j hj)

/-- Complete actual native caller execution, with the selector bank and original call arguments
protected. The original source spans may alias each other and all remaining memory may be dirty.
No source execution, catalogue, order, solver, witness or time bound is supplied as a premise. -/
theorem exec {W m n g p b : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (x : Data 640) (xn : x.regs Reg.n = n) (xD : x.regs Reg.dimension = D m)
    (xg : x.regs Reg.groups = g) (xp : x.regs Reg.prime = p) (xb : x.regs Reg.base = b)
    (hab : x.regs Reg.ab + n * n ≤ b) (hbc : x.regs Reg.bc + n * n ≤ b)
    (hac : x.regs Reg.ac + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (x.regs Reg.ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (x.regs Reg.bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (x.regs Reg.ac + q) =
      Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hx : x.Bounded W)
    (hfit : Fits W (b + 4 * windowSize n (D m) g p (rawTotal n values) + 1024)) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u v : Fin n => V (n * n + pairIndex (u, v))
    let wAC := fun u v : Fin n => V (2 * (n * n) + pairIndex (u, v))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin W program x y (timeBound (m := m) hn g p values a.mem) ∧
        y.Bounded W ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs Reg.found = 1 →
          y.regs Reg.witnessA < n ∧ y.regs Reg.witnessB < n ∧ y.regs Reg.witnessC < n ∧
          V (y.regs Reg.witnessA * n + y.regs Reg.witnessB) +
            V (n * n + (y.regs Reg.witnessB * n + y.regs Reg.witnessC)) +
            V (2 * (n * n) + (y.regs Reg.witnessA * n + y.regs Reg.witnessC)) = 0) ∧
        (∀ q, q < b ∨ b + windowSize n (D m) g p (rawTotal n values) ≤ q →
          y.mem q = x.mem q) ∧
        ∀ j : Fin 640, j.val < 160 ∨ (600 ≤ j.val ∧ j.val < 608) → y.regs j = x.regs j  := by
  obtain ⟨a, hout, y, he, yf, ys, yiff, yw, frame, regs⟩ :=
    exec_at values hlen hD hg hp hN x xn xD xg xp xb hab hbc hac vab vbc vac hfit
  exact ⟨a, hout, y, he, he.bounded hx, yf, ys, yiff, yw, frame, regs⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
