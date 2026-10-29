/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Caller
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Callee

/-!
# Executing Convolution-3SUM in caller-owned memory

The unchanged builder and instance loop read the actual source pointer and write only in the
caller-owned matrix workspace. The certified finite callee preserves the entire prefix below
that workspace, so every catalogue pointer and every remaining packed input survives each call.

## Main definitions

* `bodyAt`: complete register-argument host using the existing setup, builder and loop.
* `callerTime`: all setup, matrix, loop and finite-callee instructions, excluding halt.

## Main results

* `Callee.exec_instance`: discharge the actual generated matrix call.
* `exec_at`: exact Convolution verdict and protected-prefix frame.

These caller-layout composition proofs are original and reuse the existing finite reduction.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.Algorithms.ThreeSum

/-- The same finite loop, initialized from caller-provided raw register arguments. -/
def bodyAt {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (64 + (r + 7)) :=
  .seq (prepareAt.rename hostRegisters) (loop solver)

/-- Complete caller-entry instruction budget; the caller charges its final halt separately. -/
def callerTime (N T : ℕ) : ℕ :=
  5 * Nat.sqrt N + 26 +
    2 * sideLength N * (131 * (sideLength N * sideLength N) + T + 25)

/-- Caller initialization and the reused native kernels do not observe physical width. -/
theorem Callee.not_readsWidth_bodyAt {r : ℕ} (c : Callee r) : ¬(bodyAt c.code).ReadsWidth := by
  have hp : ¬prepareAt.ReadsWidth := by decide
  have hf : ¬fill.ReadsWidth := by decide
  have hs : ¬(solverSetup (r := r)).ReadsWidth := by
    simp only [solverSetup, Code.ReadsWidth, Op.ReadsWidth, not_false_eq_true, or_self]
  have he : ¬(finish (r := r)).ReadsWidth := by
    simp only [finish, Code.ReadsWidth, Op.bin, Op.ReadsWidth,
      reduceCtorEq, not_false_eq_true, or_self]
  simp only [bodyAt, loop, round, Code.ReadsWidth, Code.readsWidth_rename,
    hp, hf, hs, he, c.not_readsWidth, false_or, not_false_eq_true]

/-- The finite callee's matrix contract applies to the exact memory written by the builder. -/
theorem Callee.exec_instance {r w N U src workspace s : ℕ} (c : Callee r) (μ : ℕ → ℤ)
    (hvalues : ∀ i < N, |μ i| ≤ (U : ℤ))
    (hw : c.widthCoefficient * Nat.clog 2
      (workspace + 3 * (sideLength N * sideLength N) + (2 * U + 1) + sideLength N + 2) ≤ w)
    (a : Data (r + 7)) (mem : ℕ → ℕ)
    (ht : a.regs (solverArg 0) = sideLength N) (hF : a.regs (solverArg 1) = 2 * U + 1)
    (hab : a.regs (solverArg 2) = workspace)
    (hbc : a.regs (solverArg 3) = workspace + sideLength N * sideLength N)
    (hac : a.regs (solverArg 4) = workspace + 2 * (sideLength N * sideLength N))
    (hfree : a.regs (solverArg 5) = workspace + 3 * (sideLength N * sideLength N))
    (hm : a.mem = (instanceArgsAt N U src workspace s μ).filled mem
      (sideLength N * sideLength N)) :
    ∃ b, ExecWithin w c.code a b (c.time (sideLength N) (2 * U + 1)) ∧
      b.regs (solverArg 6) ≤ 1 ∧ (b.regs (solverArg 6) = 1 ↔ hit N U s μ) ∧
      ∀ p < workspace, b.mem p = mem p := by
  let t := sideLength N
  let A : Fill.Args := instanceArgsAt N U src workspace s μ
  let v : Fin t := ⟨0, by dsimp only [t, sideLength]; omega⟩
  have hmat (i j k : Fin t) := A.matrices_filled mem (by dsimp only [A, instanceArgsAt]; omega)
    (by dsimp only [A, instanceArgsAt]; omega) i j k
  have hb (i j k : Fin t) := weights_abs_le (t := t) (s := s)
    (show (0 : ℤ) ≤ U by positivity) hvalues i j k
  obtain ⟨b, he, hbool, hans, hframe⟩ := c.exec w t (2 * U + 1) workspace
    (workspace + t * t) (workspace + 2 * (t * t)) (workspace + 3 * (t * t)) a
    (weightAB N μ (2 * U + 1)) (weightBC N s μ (2 * U + 1))
    (weightAC N s μ (2 * U + 1)) (by dsimp only [t, sideLength]; omega) (by omega)
    (by omega) (by omega) (by omega) hw ht hF hab hbc hac hfree
    (fun i j => by rw [hm]; exact (hmat i j v).1)
    (fun i j => by rw [hm]; exact (hmat v i j).2.1)
    (fun i j => by rw [hm]; exact (hmat i v j).2.2)
    (fun i j => by exact_mod_cast (hb i j v).1)
    (fun i j => by exact_mod_cast (hb v i j).2.1)
    (fun i j => by exact_mod_cast (hb i v j).2.2)
  refine ⟨b, he, hbool, hans, ?_⟩
  intro p hp
  rw [hframe p hp, hm]
  apply Fill.Args.outside_filled
  all_goals dsimp only [instanceArgsAt]; omega

/-- Actual caller-argument execution with a Boolean Convolution verdict and a full prefix frame. -/
theorem exec_at {r w N U src workspace : ℕ} (c : Callee r) (μ : ℕ → ℤ)
    (x : Data (64 + (r + 7)))
    (hN : x.regs (hostRegisters len) = N) (hU : x.regs (hostRegisters upper) = U)
    (hb : x.regs (hostRegisters base) = src) (hab : x.regs (hostRegisters matAB) = workspace)
    (hbelow : src + N ≤ workspace)
    (hvalues : ∀ i < N, |μ i| ≤ (U : ℤ))
    (hmem : ∀ i < N, x.mem (src + i) = encode (μ i))
    (hidx : ∀ s < 2 * sideLength N,
      GenericRAM.Signed.Fits w ((2 * (sideLength N * sideLength N) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w (2 * (U : ℤ) + 1))
    (hnF : GenericRAM.Signed.Fits w (-(2 * (U : ℤ) + 1)))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (hsize : Fits (w + 2) (workspace + 3 * (sideLength N * sideLength N)))
    (hfill : Fits (w + 2) (4 * U + 2)) (hsqrt : Fits (w + 2) (4 * N + 4))
    (hcw : c.widthCoefficient * Nat.clog 2
      (workspace + 3 * (sideLength N * sideLength N) + (2 * U + 1) + sideLength N + 2) ≤ w + 2) :
    ∃ y, ExecWithin (w + 2) (bodyAt c.code) x y
        (callerTime N (c.time (sideLength N) (2 * U + 1))) ∧
      y.regs (hostRegisters found) ≤ 1 ∧
      (y.regs (hostRegisters found) = 1 ↔ Convolution N μ) ∧
      ∀ p < workspace, y.mem p = x.mem p := by
  obtain ⟨p, hp, hpp, hpi, hpf, hpm⟩ := exec_prepare_at (x.comap hostRegisters)
    hN hU hb hab hbelow hsize hfill hsqrt
  let a := p.extend hostRegisters x
  have ha := hp.rename (hostRegisters_injective (r := r + 7))
  have hac : a.comap hostRegisters = p := Data.comap_extend hostRegisters_injective _ _
  have hap : ParametersAt N U src workspace (a.comap hostRegisters) := by rw [hac]; exact hpp
  have hai : a.regs (hostRegisters inst) = 0 :=
    (hostRegisters_injective.extend_apply _ _ _).trans hpi
  have haf : a.regs (hostRegisters found) = 0 :=
    (hostRegisters_injective.extend_apply _ _ _).trans hpf
  obtain ⟨y, hy, _, _, hyf, hyans, hym⟩ := exec_loop_at μ c.code a hap hai haf
    (fun i hi => (congrFun hpm (src + i)).trans (hmem i hi))
    hidx hF hnF hμ hsize hbelow
    (fun s _ => c.exec_instance μ hvalues hcw)
  refine ⟨y, (ha.seq hy).mono ?_, hyf, ?_, ?_⟩
  · dsimp only [callerTime]
    omega
  · exact hyans.trans (convolution_iff_sqrt (U := (U : ℤ)) (by positivity) hvalues).symm
  · intro p hp
    exact (hym p hp).trans (congrFun hpm p)

end Cslib.Algorithms.WordRAM.ThreeSum.Host
