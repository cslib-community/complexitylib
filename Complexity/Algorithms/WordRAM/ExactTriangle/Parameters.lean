/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.NatSqrt
public import Complexity.Algorithms.ExactTriangle.Splitting

/-!
# Native ExactTriangle splitting parameters

The program computes the existing integer parameters `sOf`, `queryCap`, `pieceSize` and
`numPieces`. Both square roots call the charged native successive-squares program; all products,
quotients and ceilings are native instructions. The modulus is supplied separately by the outer
prime-selection host.

## Main definitions

* `Parameters.program`: fixed fifteen-register parameter computation.

## Main results

* `Parameters.exec`: exact outputs, explicit word fits, cost and an unchanged-memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Parameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Square-root input and arithmetic scratch. -/
abbrev arg : Fin 15 := 0
/-- Square-root result. -/
abbrev root : Fin 15 := 1
/-- Input matrix side. -/
abbrev size : Fin 15 := 6
/-- Target middle dimension. -/
abbrev dimension : Fin 15 := 7
/-- Piece-size divisor. -/
abbrev divisor : Fin 15 := 8
/-- Output floor square root of the middle dimension. -/
abbrev middleRoot : Fin 15 := 9
/-- Output query chunk capacity. -/
abbrev capacity : Fin 15 := 10
/-- Output maximum piece length. -/
abbrev pieceLength : Fin 15 := 11
/-- Output number of pieces. -/
abbrev pieces : Fin 15 := 12
/-- Square of the outer dimension. -/
abbrev area : Fin 15 := 13
/-- Constant one, outside the square-root register bank. -/
abbrev one : Fin 15 := 14

private abbrev sqrtReg : Fin 6 → Fin 15 := Fin.castLE (by decide)

private theorem sqrtReg_injective : Function.Injective sqrtReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 15 => k.val) h)

/-- Reused charged integer square root. -/
def squareRoot : Code .standard 15 := NatSqrt.program.rename (Fin.castLE (by decide))

/-- Runtime arithmetic between the square roots. -/
def between : Code .standard 15 := ram[
  middleRoot ← root; area ← size * size; arg ← area * area; arg ← arg / dimension ]

/-- Both natural ceilings use the existing `(a+b-1)/b` convention, including zero divisors. -/
def finish : Code .standard 15 := ram[
  capacity ← root; pieceLength ← middleRoot + divisor; pieceLength ← pieceLength - one;
  pieceLength ← pieceLength / divisor; pieces ← size + pieceLength;
  pieces ← pieces - one; pieces ← pieces / pieceLength ]

/-- Fixed code; only the square-root loops depend on the runtime inputs. -/
def program : Code .standard 15 :=
  .seq (ram[ one ← #1; arg ← dimension ])
    (.seq squareRoot (.seq between (.seq squareRoot finish)))

/-- Fixed native code and no physical-width reads. -/
theorem program_fixed : program.size ≤ 64 ∧ ¬program.ReadsWidth := by decide

private theorem squareRoot_preserves : ∀ i : Fin 15,
    6 ≤ i.val → squareRoot.Preserves i := by decide

/-- Compute the finite splitting parameters from actual runtime dimensions. The two explicit
ceiling-addition fits cover their temporary sums, and the fourth-power bound covers the square
formed before dividing by `D`. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 15)
    (hD : Fits w (4 * x.regs dimension + 4))
    (hN : Fits w (4 * ((x.regs size * x.regs size) * (x.regs size * x.regs size)) + 4))
    (hB : Fits w (sOf (x.regs dimension) + x.regs divisor))
    (hH : Fits w (x.regs size + pieceSize (x.regs dimension) (x.regs divisor))) :
    ∃ y, ExecWithin w program x y
        (5 * sOf (x.regs dimension) + 5 * queryCap (x.regs size) (x.regs dimension) + 27) ∧
      y.regs middleRoot = sOf (x.regs dimension) ∧
      y.regs capacity = queryCap (x.regs size) (x.regs dimension) ∧
      y.regs pieceLength = pieceSize (x.regs dimension) (x.regs divisor) ∧
      y.regs pieces = numPieces (x.regs size) (x.regs dimension) (x.regs divisor) ∧
      y.regs size = x.regs size ∧ y.regs dimension = x.regs dimension ∧
      y.regs divisor = x.regs divisor ∧ y.mem = x.mem := by
  let n := x.regs size
  let D := x.regs dimension
  let g := x.regs divisor
  let S := sOf D
  let Q := queryCap n D
  let B := pieceSize D g
  let H := numPieces n D g
  change Fits w (4 * D + 4) at hD
  change Fits w (4 * ((n * n) * (n * n)) + 4) at hN
  change Fits w (S + g) at hB
  change Fits w (n + B) at hH
  have h1 : Fits w 1 := hD.of_le (by omega)
  let a := x.set one 1 |>.set arg D
  have hstart : ExecWithin (B := .standard) w (ram[ one ← #1; arg ← dimension ]) x a 2 := by
    have hfit : Fits w D := hD.of_le (by dsimp [D]; omega)
    ram_eval [a, D, h1, hfit, one, arg, dimension, Fin.mk.injEq]
  have haD : a.regs arg = D := by simp [a]
  obtain ⟨b, hb, hbroot, -, hbm, -⟩ := NatSqrt.exec_rename sqrtReg sqrtReg_injective a
    (by change Fits w (4 * a.regs arg + 4); rw [haD]; exact hD)
  change b.regs root = S at hbroot
  change ExecWithin w squareRoot a b (5 * Nat.sqrt (a.regs arg) + 7) at hb
  have hbreg (i : Fin 15) (hi : i = size ∨ i = dimension ∨ i = divisor) :
      b.regs i = x.regs i := by
    have hhi : 6 ≤ i.val := by rcases hi with rfl | rfl | rfl <;> decide
    have h := hb.regs_eq (squareRoot_preserves i hhi)
    exact h.trans (by
      rcases hi with rfl | rfl | rfl <;>
        simp +decide [a, size, dimension, divisor, one, arg])
  have hbsize : b.regs size = n := hbreg size (by simp)
  have hbD : b.regs dimension = D := hbreg dimension (by simp)
  have hbg : b.regs divisor = g := hbreg divisor (by simp)
  have hbone : b.regs one = 1 := by
    exact (hb.regs_eq (squareRoot_preserves one (by decide))).trans (by simp +decide [a, one, arg])
  have hnarea : n * n ≤ (n * n) * (n * n) := by
    by_cases h : n * n = 0
    · simp [h]
    · exact Nat.le_mul_of_pos_right _ (by omega)
  have hafit : Fits w (n * n) := hN.of_le (by omega)
  have hn4 : Fits w ((n * n) * (n * n)) := hN.of_le (by omega)
  have hquot : Fits w ((n * n) * (n * n) / D) := hn4.of_le (Nat.div_le_self ..)
  let c := b.set middleRoot S |>.set area (n * n)
    |>.set arg ((n * n) * (n * n)) |>.set arg ((n * n) * (n * n) / D)
  have hbetween : ExecWithin w between b c 4 := by
    ram_eval [between, c, hbroot, hbsize, hbD, hafit, hn4, hquot,
      middleRoot, area, arg, root, size, dimension, Fin.mk.injEq]
  have hcarg : c.regs arg = (n * n) * (n * n) / D := by simp [c]
  obtain ⟨d, hd, hdroot, -, hdm, -⟩ := NatSqrt.exec_rename sqrtReg sqrtReg_injective c (by
    change Fits w (4 * c.regs arg + 4)
    rw [hcarg]
    exact hN.of_le (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.div_le_self ..)) 4))
  have hdroot' : d.regs root = Q := by
    change d.regs root = Nat.sqrt (c.regs arg) at hdroot
    rw [hcarg] at hdroot
    simpa only [Q, queryCap, pow_two] using hdroot
  change ExecWithin w squareRoot c d (5 * Nat.sqrt (c.regs arg) + 7) at hd
  have hdreg (i : Fin 15) (hi : i = size ∨ i = dimension ∨ i = divisor ∨ i = one) :
      d.regs i = b.regs i := by
    have hhi : 6 ≤ i.val := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    have h := hd.regs_eq (squareRoot_preserves i hhi)
    exact h.trans (by
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp +decide [c, size, dimension, divisor, one, middleRoot, area, arg])
  have hdn : d.regs size = n := (hdreg size (by simp)).trans hbsize
  have hdg : d.regs divisor = g := (hdreg divisor (by simp)).trans hbg
  have hdo : d.regs one = 1 := (hdreg one (by simp)).trans hbone
  have hdS : d.regs middleRoot = S := by
    exact (hd.regs_eq (squareRoot_preserves middleRoot (by decide))).trans (by
      simp +decide [c, middleRoot, area, arg])
  let y := d.set capacity Q |>.set pieceLength (S + g) |>.set pieceLength (S + g - 1)
    |>.set pieceLength B |>.set pieces (n + B) |>.set pieces (n + B - 1) |>.set pieces H
  have hfinish : ExecWithin w finish d y 7 := by
    have hsubB : Fits w (S + g - 1) := hB.of_le (Nat.sub_le ..)
    have hdivB : Fits w ((S + g - 1) / g) := hsubB.of_le (Nat.div_le_self ..)
    have hsubH : Fits w (n + B - 1) := hH.of_le (Nat.sub_le ..)
    have hdivH : Fits w ((n + B - 1) / B) := hsubH.of_le (Nat.div_le_self ..)
    simp only [B, pieceSize, Nat.ceilDiv_eq_add_pred_div, S, sOf]
      at hB hH hsubB hdivB hsubH hdivH
    ram_eval [finish, y, hdroot', hdS, hdn, hdg, hdo, B, H, pieceSize, numPieces,
      Nat.ceilDiv_eq_add_pred_div, S, sOf, hB, hH, hsubB, hdivB, hsubH, hdivH,
      capacity, root, pieceLength, middleRoot, divisor, pieces, size, one, Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hstart.seq (hb.seq (hbetween.seq (hd.seq hfinish))) using 1
    · rfl
    · simp only [haD, hcarg, sOf, queryCap, pow_two]
      dsimp [n, D]
      omega
  · change y.regs middleRoot = S
    simp +decide [y, capacity, pieceLength, pieces, middleRoot, hdS]
  · change y.regs capacity = Q
    simp +decide [y, capacity, pieceLength, pieces]
  · change y.regs pieceLength = B
    simp +decide [y, capacity, pieceLength, pieces]
  · change y.regs pieces = H
    simp [y]
  · simpa +decide [y, capacity, pieceLength, pieces, size] using hdn
  · have h := (hdreg dimension (by simp)).trans hbD
    simpa +decide [y, capacity, pieceLength, pieces, dimension] using h
  · simpa +decide [y, capacity, pieceLength, pieces, divisor] using hdg
  · exact hdm.trans hbm

end Cslib.Algorithms.WordRAM.ExactTriangle.Parameters
