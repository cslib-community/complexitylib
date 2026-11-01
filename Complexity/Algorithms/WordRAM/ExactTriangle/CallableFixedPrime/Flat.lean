/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Input

/-!
# Initialized halting caller-safe fixed-prime computation

The same final state witnesses the actual initialized prefix, halt, verdict, original
coordinates and global failed-scan accounting. Fourteen real header/pointer instructions
precede the complete caller program, and the final halt is charged. This remains a fixed-prime
component with explicit thin geometry, not parameter/prime selection or the 3SUM endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem pow_sourceWidth_add_two (n D g p T : ℕ) :
    2 ^ (sourceWidth n D g p T + 2) = 4 * windowSize n D g p T := by
  simp [windowSize, pow_add, Nat.mul_comm]

private theorem input_low_admission {m n g p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) :
    InputFits (sourceWidth n (D m) g p (rawTotal n values) + 2)
        (PreparationInput.input n (D m) g p values) ∧
      Fits (sourceWidth n (D m) g p (rawTotal n values) + 2)
        (n + D m + g + p + 5 + 3 * (n * n) + 1024) := by
  have hi := input_fits_source (m := m) (g := g) (p := p) values hlen
    (natAbs_le_rawTotal values hlen)
  have hI := inputEnd_le_window (m := m) (g := g) (p := p) values hlen
  obtain ⟨hS, -, hc⟩ := source_bounds n (D m) g p (rawTotal n values)
  refine ⟨hi.mono (by omega), ?_⟩
  change _ < 2 ^ (sourceWidth n (D m) g p (rawTotal n values) + 2)
  rw [pow_sourceWidth_add_two]
  omega

/-- Fully initialized same-state prefix and halt. The width guarantee also establishes original
input fit; no producer state, prepared catalogue, layout, solver or run law is an input. -/
theorem runs_input {W m n g p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hW : inputWidth n (D m) g p values ≤ W) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u v : Fin n => V (n * n + pairIndex (u, v))
    let wAC := fun u v : Fin n => V (2 * (n * n) + pairIndex (u, v))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    InputFits W (PreparationInput.input n (D m) g p values) ∧
      ∃ a : Data 64,
        Instances.Output n (D m) g p V
          (.init (PreparationInput.input n (D m) g p values)) a ∧
        ∃ y t, t + 1 ≤ timeBound (m := m) hn g p values a.mem + 15 ∧
          Runs W (entryProgram.program Reg.found)
            (State.init (PreparationInput.input n (D m) g p values)) ⟨entryProgram.size, y⟩ t ∧
          Executes W (entryProgram.program Reg.found)
            (State.init (PreparationInput.input n (D m) g p values)) (y.regs Reg.found) (t + 1) ∧
          y.Bounded W ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
          y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
          (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
          (y.regs Reg.found = 1 → ∃ u v c : Fin n,
            y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
            y.regs Reg.witnessC = c.val ∧ weightSum wAB wBC wAC u v c = 0) ∧
          (∀ q, q < workspaceBase n ∨
            workspaceBase n + windowSize n (D m) g p (rawTotal n values) ≤ q →
            y.mem q = (Data.init (PreparationInput.input n (D m) g p values) : Data 640).mem q) ∧
          ∀ j : Fin 640, j.val < 160 → y.regs j = 0 := by
  let T := rawTotal n values
  let M := windowSize n (D m) g p T
  let b := workspaceBase n
  let w₀ := sourceWidth n (D m) g p T + 2
  have fit : Fits W (b + 4 * M + 4 * M + 1024) := admission_fits hW
  have hw₀ : w₀ ≤ W := by
    have h4M : Fits W (4 * M) := fit.of_le (by omega)
    change 4 * M < 2 ^ W at h4M
    have hpw : 2 ^ w₀ = 4 * M := pow_sourceWidth_add_two n (D m) g p T
    by_contra h
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : W ≤ w₀)
    rw [hpw] at hpow
    omega
  obtain ⟨hi₀, hinitfit⟩ := input_low_admission (m := m) (g := g) (p := p) values hlen
  obtain ⟨x, hinit, xmem, xn, xD, xg, xp, xab, xbc, xac, xb⟩ := exec_entryHeader values hinitfit
  have hi : InputFits W (PreparationInput.input n (D m) g p values) := hi₀.mono hw₀
  have hx₀ : x.Bounded w₀ := hinit.bounded (Data.Bounded.init hi₀)
  have hx : x.Bounded W := ⟨fun i => (hx₀.1 i).mono hw₀, fun q => (hx₀.2 q).mono hw₀⟩
  have hinitial : ExecWithin W entryHeader
      (.init (PreparationInput.input n (D m) g p values)) x 14 :=
    ExecWithin.mono_width entryHeader_fixed.2 hinit hw₀
  have vab (q : ℕ) (hq : q < n * n) :
      x.mem (x.regs Reg.ab + q) = Signed.encode (values.getD q 0) := by
    rw [xab, xmem]
    exact PreparationInput.input_word n (D m) g p values q
  have vbc (q : ℕ) (hq : q < n * n) :
      x.mem (x.regs Reg.bc + q) = Signed.encode (values.getD (n * n + q) 0) := by
    rw [xbc, xmem]
    simpa only [Data.init, Nat.add_assoc] using
      PreparationInput.input_word n (D m) g p values (n * n + q)
  have vac (q : ℕ) (hq : q < n * n) : x.mem (x.regs Reg.ac + q) =
      Signed.encode (values.getD (2 * (n * n) + q) 0) := by
    rw [xac, xmem]
    simpa only [Data.init, two_mul, Nat.add_assoc] using
      PreparationInput.input_word n (D m) g p values (2 * (n * n) + q)
  obtain ⟨a, hout, y, hy, ybound, yf, ys, yiff, yw, yframe, -⟩ := exec values hlen hD hg hp hN
    x xn xD xg xp xb (by rw [xab]; dsimp only [workspaceBase]; omega)
    (by rw [xbc]; dsimp only [workspaceBase]; omega)
    (by rw [xac]; dsimp only [workspaceBase]; omega) vab vbc vac hx
    (fit.of_le (by dsimp only [b, M, T] at *; omega))
  have he : ExecWithin W entryProgram
      (.init (PreparationInput.input n (D m) g p values)) y
      (14 + timeBound (m := m) _ g p values a.mem) := hinitial.seq hy
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, a, hout, y, t, ?_, ?_, ?_, ybound, yf, ys, yiff, ?_, ?_, ?_⟩
  · exact (Nat.add_le_add_right ht 1).trans_eq (by ring)
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := entryProgram.program Reg.found) (Program.Contains.self _).append_left
  · simpa only [State.init] using hex.executes Reg.found
  · intro hf
    obtain ⟨ha, hb, hc, hz⟩ := yw hf
    exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl, rfl, rfl, hz⟩
  · intro q hq
    exact (yframe q hq).trans (congrFun xmem q)
  · intro j hj
    exact hex.regs_eq (entryProgram_preserves_selector j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
