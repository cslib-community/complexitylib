/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.DyadicCost

/-!
# Selected-prime initialized executions with a strict-subcubic charge

The existing real callable program supplies original signed verdicts and witnesses. Its actual
initialized prefix and halt are bounded by the natural dyadic time function, which is uniformly
strict-subcubic for polynomial original weights. The sufficient physical width is derived from
the original inputs. Runtime p is still a selected prime supplied in the input; parameter/prime
execution and final 3SUM composition remain separate.

## Main results

* `exists_dyadic_runs_threshold`: a shared coefficient and threshold per weight exponent, with
  actual same-state prefix/halt, natural time allowance, exact verdict/witness and input frame.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open ParameterChoice

-- Only the existing fixed fast-threshold numeral is normalized during proof transport.
set_option exponentiation.threshold 1296 in
/-- Actual initialized computation, not a supplied run law. The positive coefficient and
threshold are chosen before every original input, prime and width. Selected-prime membership
is a performance hypothesis on runtime p; no layout, clock or execution certificate is supplied.
The allowance conservatively includes parameter/selector work not executed by this subroutine. -/
theorem exists_dyadic_runs_threshold {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ^ 1296 ≤ N ∧
      ∀ n ≥ N, ∀ (F : ℕ) (values : List ℤ) (p W : ℕ),
        values.length = 3 * (n * n) → (∀ z ∈ values, z.natAbs ≤ F) → F ≤ (n + 2) ^ κ →
        IsSelectedPrime
          (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
          (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
          (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p →
        (24664 * (κ + 9) + 19) * Nat.clog 2 (n + 2) ≤ W →
        InputFits W (PreparationInput.input n (window n) (groups n) p values) ∧
          ∃ y t,
            Runs W (entryProgram.program Reg.found)
              (State.init (PreparationInput.input n (window n) (groups n) p values))
              ⟨entryProgram.size, y⟩ t ∧
            Executes W (entryProgram.program Reg.found)
              (State.init (PreparationInput.input n (window n) (groups n) p values))
              (y.regs Reg.found) (t + 1) ∧
            t + 1 ≤ dyadicTime n F ∧
            (dyadicTime n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) ∧
            y.Bounded W ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
            (y.regs Reg.found = 1 ↔ HasZeroTriangle
              (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
              (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
              (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0)) ∧
            (y.regs Reg.found = 1 → ∃ u v c : Fin n,
              y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
              y.regs Reg.witnessC = c.val ∧
              weightSum (fun a b => values.getD (pairIndex (a, b)) 0)
                (fun a b => values.getD (n * n + pairIndex (a, b)) 0)
                (fun a b => values.getD (2 * (n * n) + pairIndex (a, b)) 0) u v c = 0) ∧
            ∀ q < workspaceBase n, y.mem q =
              (Data.init (PreparationInput.input n (window n) (groups n) p values) :
                Data 640).mem q := by
  obtain ⟨C, hC, N, hN, hc⟩ := exists_dyadicTime_subcubic_bound hκ
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hnN F values p W hlen hv hF hp hW
  have hn : 0 < n := (Nat.two_pow_pos 1296).trans_le (hN.trans hnN)
  have hf := (blocks_pos_iff n).mpr (hN.trans hnN)
  have hd := window_le hn
  have hg := (groups_le_window n).trans hd
  have hpN : p ≤ n := (Nat.le_self_pow (by decide : 2 ≠ 0) p).trans
    ((Nat.mem_sqrtPrimeWindow_iff_sq.mp hp.1).2.2.le.trans hd)
  have hw : inputWidth n (window n) (groups n) p values ≤ W :=
    (inputWidth_le_log values hlen hv hd hg hpN hF).trans hW
  obtain ⟨hi, a, hout, y, t, ht, hr, he, hbound, hflag, hscan, hiff, hwitness, hframe, hregs⟩ :=
    runs_input (m := level n) values hlen (window_ge_sixteen hf)
      (one_le_groups n) hp.1 (geometry hn) hw
  have hb := timeBound_le_dyadicTime hf values hlen hv hp a.mem
  have ht' : t + 1 ≤ dyadicTime n F := by omega
  exact ⟨hi, y, t, hr, he, ht', hc n hnN F hF, hbound, hflag, hiff, hwitness,
    fun q hq => hframe q (Or.inl hq)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
