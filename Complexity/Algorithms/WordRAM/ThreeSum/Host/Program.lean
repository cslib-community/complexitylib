/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Loop
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Width
public import Complexity.Computability.WordRAM.Compile

/-!
# The complete native Convolution-3SUM host

The host computes its parameters from the ordinary input header, constructs every instance,
executes the supplied finite solver program in a disjoint register bank, accumulates its answer,
and halts. The source word width is logarithmic for polynomially bounded integer inputs.

This is a conditional native reduction: the caller must prove execution, correctness and input
preservation of the actual solver code at the stated width and charged budget. The host does not
supply a fast Exact Triangle solver or finish the subquadratic 3SUM endpoint.

The construction directly adapts Anthropic's pinned
[`c3Body`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Host.lean).

## Main definitions

* `Host.body`: initialization and the complete native instance loop.
* `Host.time`: charged time, including the final halt.

## Main results

* `Host.runs_input`: actual initialized native execution, output and input preservation.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum

/-- The code depends only on the fixed magnitude exponent and the supplied finite solver. -/
def body {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) :
    Code .standard (64 + (r + 7)) :=
  .seq ((prepare κ).rename hostRegisters) (loop solver)

/-- Complete charged instruction budget, including the halt and every solver invocation. -/
def time (κ N T : ℕ) : ℕ :=
  ChanHe.Parameters.time κ N ((N + 2) ^ κ) + 5 * Nat.sqrt N + 27 +
    2 * sideLength N * (131 * (sideLength N * sideLength N) + T + 25)

/-- Solver time is multiplied by `2t`; all host work is `Oκ((N+1)t + log(N+2))`. -/
theorem time_bound (κ N T : ℕ) : time κ N T ≤
    2 * sideLength N * T + 1000 * (N + 1) * sideLength N +
      (400 * κ + 3000) * Nat.clog 2 (N + 2) := by
  have hp := ChanHe.Parameters.time_bound κ N
  have ha := area_le N
  have ht : 1 ≤ sideLength N := by dsimp [sideLength]; omega
  have hmul := Nat.mul_le_mul_left (262 * sideLength N) ha
  dsimp only [time]
  dsimp only [sideLength] at *
  nlinarith

/-- Native initialized execution at target width `w+2`. The execution witness identifies the
actual pre-halt state containing the output. The sole solver premise is an execution theorem
for the concrete `solver` argument, on the matrices the host actually constructs. -/
theorem runs_input {κ w r T : ℕ} (input : List ℤ) (solver : Code .standard (r + 7))
    (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    (hsolver : let N := input.length; let U := (N + 2) ^ κ;
      let μ : ℕ → ℤ := fun i => input.getD i 0;
      ∀ s < 2 * sideLength N, ∀ (a : Data (r + 7)) (mem : ℕ → ℕ),
      a.regs (solverArg 0) = sideLength N → a.regs (solverArg 1) = 2 * U + 1 →
      a.regs (solverArg 2) = N + 1 →
      a.regs (solverArg 3) = N + 1 + sideLength N * sideLength N →
      a.regs (solverArg 4) = N + 1 + 2 * (sideLength N * sideLength N) →
      a.regs (solverArg 5) = N + 1 + 3 * (sideLength N * sideLength N) →
      a.mem = (instanceArgs N U s μ).filled mem (sideLength N * sideLength N) →
      ∃ b, ExecWithin (w + 2) solver a b T ∧ b.regs (solverArg 6) ≤ 1 ∧
        (b.regs (solverArg 6) = 1 ↔ hit N U s μ) ∧
        (∀ a < N + 1, b.mem a = mem a)) :
    ∃ y t, t ≤ time κ input.length T ∧
      Runs (w + 2) ((body κ solver).program (hostRegisters found))
        (State.init (input.map encode)) ⟨(body κ solver).size, y⟩ (t - 1) ∧
      Executes (w + 2) ((body κ solver).program (hostRegisters found))
        (State.init (input.map encode)) (y.regs (hostRegisters found)) t ∧
      y.regs (hostRegisters found) ≤ 1 ∧
      (y.regs (hostRegisters found) = 1 ↔
        Convolution input.length (fun i => input.getD i 0)) ∧
      (∀ a < input.length + 1,
        y.mem a = (Data.init (input.map encode) : Data (64 + (r + 7))).mem a) ∧
      y.Bounded (w + 2) := by
  let N := input.length
  let U := (N + 2) ^ κ
  let μ : ℕ → ℤ := fun i => input.getD i 0
  let x : Data (64 + (r + 7)) := Data.init (input.map encode)
  have hmem : ∀ i < N, x.mem (1 + i) = encode (μ i) := by
    intro i hi
    have hm : i < (input.map encode).length := by simpa only [List.length_map] using hi
    simp only [x, μ, Nat.add_comm 1, Data.init_mem_succ, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hm,
      List.getElem?_eq_getElem hi, List.getElem_map, Option.getD_some]
  have hμ : ∀ i < N, |μ i| ≤ (U : ℤ) := by
    intro i hi
    simpa only [μ, U, N, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] using hvalues input[i] (List.getElem_mem hi)
  have hpw : ChanHe.Parameters.width κ N ≤ w + 2 :=
    (Nat.le_add_right _ 4).trans ((parameters_width_le κ N).trans (hw.trans (by omega)))
  have hf := layout_fits hw
  have hbudget : Fits (w + 2) (ChanHe.Parameters.Math.budget N U) :=
    ChanHe.Parameters.budget_fits hpw
  obtain ⟨p, hp, hpp, hpi, hpf, hpm⟩ := exec_prepare κ (x.comap hostRegisters)
    (by simpa only [x, Data.comap_mem, Data.init_mem_zero, List.length_map] using hbudget)
    (by simpa only [x, Data.comap_mem, Data.init_mem_zero, List.length_map] using
      hf.1.mono (show w ≤ w + 2 by omega))
    (by simpa only [x, Data.comap_mem, Data.init_mem_zero, List.length_map] using
      hf.2.mono (show w ≤ w + 2 by omega))
  simp only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] at hp hpp
  let a := p.extend hostRegisters x
  have ha := hp.rename (hostRegisters_injective (r := r + 7))
  have hac : a.comap hostRegisters = p := Data.comap_extend hostRegisters_injective _ _
  have hap : Parameters N U (a.comap hostRegisters) := by rw [hac]; exact hpp
  have hai : a.regs (hostRegisters inst) = 0 :=
    hostRegisters_injective.extend_apply _ _ _ |>.trans hpi
  have haf : a.regs (hostRegisters found) = 0 :=
    hostRegisters_injective.extend_apply _ _ _ |>.trans hpf
  have ham : a.mem = x.mem := hpm
  have hinput : ∀ i < N, a.mem (1 + i) = encode (μ i) := by
    intro i hi
    rw [ham]
    exact hmem i hi
  obtain ⟨y, hy, -, -, hyf, hyans, hym⟩ := exec_loop μ solver a hap hai haf hinput
    (fun s hs => index_fits hw hs) (filler_fits hw).1 (filler_fits hw).2
    (fun i hi => value_fits hw (hμ i hi))
    (hf.1.mono (show w ≤ w + 2 by omega)) hsolver
  have hans : y.regs (hostRegisters found) = 1 ↔ Convolution N μ :=
    hyans.trans (convolution_iff_sqrt (U := (U : ℤ)) (by positivity) hμ).symm
  obtain ⟨n, hn, he⟩ := ha.seq hy
  have hr := he.runs (pc := 0) (p := (body κ solver).program (hostRegisters found))
    (Program.Contains.self _).append_left
  have hi := ChanHe.Parameters.inputFits input hpw hvalues
  refine ⟨y, n + 1, ?_, ?_, he.executes (hostRegisters found), hyf, hans, ?_, ?_⟩
  · dsimp only [time, N] at hn ⊢
    omega
  · simpa only [Nat.add_sub_cancel, Nat.zero_add, body, State.init] using hr
  · intro a ha
    exact (hym a ha).trans (congrFun ham a)
  · exact hr.bounded_init hi

end Cslib.Algorithms.WordRAM.ThreeSum.Host
