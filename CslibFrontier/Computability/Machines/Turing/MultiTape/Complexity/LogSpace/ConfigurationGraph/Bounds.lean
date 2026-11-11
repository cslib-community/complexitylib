/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Radices accommodating a space bound

A source machine that visits at most `S` work cells along every computation prefix has only
views whose registers fit any radix `B` with `n + 2 ≤ B`, room for the finite control and
`3 ^ (4 * S + 1) ≤ B` (`Turing.MultiTapeNTM.ConfigurationGraph.fits_of_runsInSpace_of_le`).
For logarithmic space a fixed exponent, depending only on the source machine and its space
constant, gives such a radix `(n + 2) ^ D`. Thus the exact compact graph then has polynomially
many vertices, and its local routines take only logarithmically many stored bits.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.reachable_lt_pow_of_runsInSpace`: polynomial ambient bound
  on reachable configuration vertices.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_of_runsInSpace_of_le`: every reachable view fits a
  large enough radix.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_of_runsInSpace`: the logarithmic-space radix.
* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace`: exact graph.
* `Turing.MultiTapeNTM.ConfigurationGraph.vertexBound_eq_pow`: natural-polynomial vertex bound.
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State] {ntm : MultiTapeNTM k Bool State}
  {w : List Bool}

/-- **Every reachable view fits a large enough radix**: one above the input positions, the
finite tags, and the ternary stack codes of `4 * S + 1` cells, for a source that visits at most
`S` work cells along every computation prefix. -/
theorem fits_of_runsInSpace_of_le {S B : ℕ} (hs : ntm.RunsInSpace w S)
    (hn : w.length + 2 ≤ B) (hc : Fintype.card (Option State) < B) (h3 : 3 < B)
    (hstack : 3 ^ (4 * S + 1) ≤ B) {v : FiniteCfg k Bool State}
    (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    Fits B (registers v) := by
  have hi := input_of_reachable hv
  intro i
  cases i with
  | inputPos => exact v.inputPos.isLt.trans_le (hi ▸ hn)
  | control => exact (Fintype.equivFin (Option State) v.state).isLt.trans hc
  | output => exact (outputCode_lt _).trans h3
  | head i => exact (symbolCode_lt _).trans h3
  | left i | right i =>
    have ht := spaceUsed_workTapes_le hs hv i
    have hlen : (v.workTapes i).left.length ≤ 4 * S + 1 ∧
        (v.workTapes i).right.length ≤ 4 * S + 1 := by
      simp only [BiTape.spaceUsed] at ht
      omega
    first
    | exact (stackCode_lt _).trans_le ((Nat.pow_le_pow_right (by omega) hlen.1).trans hstack)
    | exact (stackCode_lt _).trans_le ((Nat.pow_le_pow_right (by omega) hlen.2).trans hstack)

/-- A generous fixed radix exponent for a machine using `c * (log2 n + 1)` work cells. -/
def radixExponent (State : Type) [Fintype State] (c : ℕ) : ℕ :=
  16 * c + Fintype.card (Option State) + 4

/-- The ambient vertex count is exactly a fixed natural power of `n+2`. -/
theorem vertexBound_eq_pow (D n : ℕ) :
    vertexBound (k := k) (radix D n) = (n + 2) ^ (D * Fintype.card (Register k)) :=
  (pow_mul _ _ _).symm

private theorem stack_bound (c n : ℕ) :
    3 ^ (4 * (c * (Nat.log2 n + 1)) + 1) ≤ radix (radixExponent State c) n := by
  have hlog : 2 ^ (Nat.log2 n + 1) ≤ (n + 2) ^ 2 :=
    (Nat.two_pow_log2_succ_le n).trans (by nlinarith)
  calc
    3 ^ (4 * (c * (Nat.log2 n + 1)) + 1)
      ≤ 4 ^ (4 * (c * (Nat.log2 n + 1)) + 1) := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (8 * (c * (Nat.log2 n + 1)) + 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
      congr 1
      ring
    _ ≤ 2 ^ ((8 * c + 2) * (Nat.log2 n + 1)) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    _ = (2 ^ (Nat.log2 n + 1)) ^ (8 * c + 2) := by rw [← pow_mul]; congr 1; ring
    _ ≤ ((n + 2) ^ 2) ^ (8 * c + 2) := Nat.pow_le_pow_left hlog _
    _ ≤ radix (radixExponent State c) n := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by simp only [radixExponent]; omega)

/-- Every view reachable under the native logarithmic space bound fits the fixed radix. -/
theorem fits_of_runsInSpace (c : ℕ) (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1)))
    {v : FiniteCfg k Bool State}
    (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    Fits (radix (radixExponent State c) w.length) (registers v) := by
  have hD : 2 ≤ radixExponent State c := by simp only [radixExponent]; omega
  have hbase : w.length + 2 ≤ radix (radixExponent State c) w.length := by
    calc
      w.length + 2 = (w.length + 2) ^ 1 := by simp
      _ ≤ (w.length + 2) ^ radixExponent State c := Nat.pow_le_pow_right (by omega) (by omega)
  have hthree : 3 < radix (radixExponent State c) w.length := by
    have hp := Nat.pow_le_pow_left (show 2 ≤ w.length + 2 by omega) 2
    have he := Nat.pow_le_pow_right (show 1 ≤ w.length + 2 by omega) hD
    change 3 < (w.length + 2) ^ radixExponent State c
    omega
  have hcard : Fintype.card (Option State) < radix (radixExponent State c) w.length := by
    have hp := (Nat.lt_two_pow_self :
      Fintype.card (Option State) < 2 ^ Fintype.card (Option State))
    have he : 2 ^ Fintype.card (Option State) ≤ radix (radixExponent State c) w.length :=
      (Nat.pow_le_pow_left (by omega : 2 ≤ w.length + 2) _).trans
        (Nat.pow_le_pow_right (by omega) (by simp only [radixExponent]; omega))
    exact hp.trans_le he
  exact fits_of_runsInSpace_of_le hs hbase hcard hthree (stack_bound c w.length) hv

/-- Every reachable ID is strictly below a natural polynomial in input length. -/
theorem vertexID_lt_pow_of_runsInSpace (c : ℕ)
    (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) {v : FiniteCfg k Bool State}
    (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    vertexID (radix (radixExponent State c) w.length) v <
      (w.length + 2) ^ (radixExponent State c * Fintype.card (Register k)) := by
  have h := vertexID_lt (fits_of_runsInSpace c hs hv)
  rwa [vertexBound_eq_pow] at h

/-- Binary vertex IDs need only logarithmically many bits. -/
theorem length_vertexID_le_of_runsInSpace (c : ℕ)
    (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) {v : FiniteCfg k Bool State}
    (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    (MultiTapeTM.encNat (vertexID (radix (radixExponent State c) w.length) v)).length ≤
      (radixExponent State c * Fintype.card (Register k) + 1) *
        (Nat.log2 (w.length + 1) + 1) :=
  MultiTapeTM.length_encNat_le_of_le_pow (N := w.length + 1)
    (Nat.le_of_lt (vertexID_lt_pow_of_runsInSpace c hs hv))

/-- Every vertex reachable in the compact graph satisfies the polynomial ambient bound. -/
theorem reachable_lt_pow_of_runsInSpace (c : ℕ)
    (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) {u : ℕ}
    (hu : Relation.ReflTransGen (Edge ntm (radix (radixExponent State c) w.length) w)
      (startID ntm (radix (radixExponent State c) w.length)) u) :
    u < (w.length + 2) ^ (radixExponent State c * Fintype.card (Register k)) := by
  obtain ⟨v, hv, rfl⟩ := (reachable_iff (fun _ h => fits_of_runsInSpace c hs h) u).mp hu
  exact vertexID_lt_pow_of_runsInSpace c hs hv

/-- A logarithmic native space bound supplies the exact polynomial compact graph. -/
theorem accepts_iff_reachable_bad_of_runsInSpace (c : ℕ)
    (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    ntm.Accepts w ↔ ∃ u,
      Relation.ReflTransGen (Edge ntm (radix (radixExponent State c) w.length) w)
        (startID ntm (radix (radixExponent State c) w.length)) u ∧
      bad (k := k) (State := State) (radix (radixExponent State c) w.length) w.length u =
        true :=
  accepts_iff_reachable_bad fun _ h => fits_of_runsInSpace c hs h

end Turing.MultiTapeNTM.ConfigurationGraph
