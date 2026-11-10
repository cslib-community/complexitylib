/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds

/-!
# Radix rounds

A simulation that cannot compute the space of its source can still find a compact configuration
graph that represents every reachable view: it tries the radices `startRadix State n`,
`4 * startRadix State n`, `16 * startRadix State n`, … in turn and keeps the first one in whose
graph no reachable vertex overflows
(`Turing.MultiTapeNTM.ConfigurationGraph.fits_of_not_overflow`). The space of the source then only
bounds the number of rounds: a source visiting at most `S` work cells fits every radix from round
`4 * S + 1` on (`Turing.MultiTapeNTM.ConfigurationGraph.fits_roundRadix_of_runsInSpace`), and the
vertices of round `j` have `O(j + log₂ n)` bits
(`Turing.MultiTapeNTM.ConfigurationGraph.vertexWidth_roundRadix_le`). Inductive counting grows its
radix this way, so that its space bound need not be constructible [Immerman1988].

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.startRadix`: the first radix, above every input position
  and finite tag.
* `Turing.MultiTapeNTM.ConfigurationGraph.roundRadix`: the radix of round `j`, `4 ^ j` times the
  first.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.fits_init`,
  `Turing.MultiTapeNTM.ConfigurationGraph.startID_lt`: the start view fits every radix above the
  finite tags, so in particular every round.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_roundRadix_of_runsInSpace`: a source visiting at
  most `S` work cells fits every round from `4 * S + 1` on.
* `Turing.MultiTapeNTM.ConfigurationGraph.roundRadix_le_two_pow`,
  `Turing.MultiTapeNTM.ConfigurationGraph.vertexWidth_roundRadix_le`: round `j` has a radix below
  `2 ^ (2 * j + log₂ n + O(1))` and vertices of `O(j + log₂ n)` bits.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State] {ntm : MultiTapeNTM k Bool State} {B : ℕ}
  {w : List Bool}

/-! ### The radices -/

variable (State) in
/-- The first radix tried: above every input position and every finite tag. -/
def startRadix (n : ℕ) : ℕ := (n + 2) * 2 ^ (Fintype.card (Option State) + 2)

theorem le_startRadix (n : ℕ) : n + 2 ≤ startRadix State n :=
  Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

theorem card_lt_startRadix (n : ℕ) : Fintype.card (Option State) + 3 < startRadix State n := by
  have hm : 2 ^ (Fintype.card (Option State) + 2) ≤ startRadix State n :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hp : 2 ^ (Fintype.card (Option State) + 2) = 4 * 2 ^ Fintype.card (Option State) := by
    rw [pow_add]
    ring
  have h2 := Nat.lt_two_pow_self (n := Fintype.card (Option State))
  omega

variable (State) in
/-- The radix of round `j`: the first radix times `4 ^ j`. -/
def roundRadix (n j : ℕ) : ℕ := 4 ^ j * startRadix State n

theorem roundRadix_zero (n : ℕ) : roundRadix State n 0 = startRadix State n := by
  simp [roundRadix]

theorem roundRadix_succ (n j : ℕ) : roundRadix State n (j + 1) = 4 * roundRadix State n j := by
  simp only [roundRadix, pow_succ]
  ring

theorem startRadix_le_roundRadix (n j : ℕ) : startRadix State n ≤ roundRadix State n j :=
  Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)

theorem card_lt_roundRadix (n j : ℕ) : Fintype.card (Option State) + 1 < roundRadix State n j :=
  (by have := card_lt_startRadix (State := State) n; omega : Fintype.card (Option State) + 1 <
    startRadix State n).trans_le (startRadix_le_roundRadix n j)

theorem roundRadix_mono (n : ℕ) {j j' : ℕ} (h : j ≤ j') :
    roundRadix State n j ≤ roundRadix State n j' :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

/-- Larger radices have larger ambient graphs. -/
theorem vertexBound_mono {B B' : ℕ} (h : B ≤ B') :
    vertexBound (k := k) B ≤ vertexBound (k := k) B' :=
  Nat.pow_le_pow_left h _

/-- Round `j` has a radix below `2 ^ (2 * j + log₂ n + O(1))`. -/
theorem roundRadix_le_two_pow (n j : ℕ) :
    roundRadix State n j ≤ 2 ^ (2 * j + Nat.log2 n + Fintype.card (Option State) + 4) := by
  have hn : n + 2 ≤ 2 ^ (Nat.log2 n + 2) := by
    have := Nat.lt_log2_self (n := n)
    rw [pow_succ]
    omega
  have h4 : (4 : ℕ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  calc roundRadix State n j = 2 ^ (2 * j) * ((n + 2) * 2 ^ (Fintype.card (Option State) + 2)) := by
        rw [roundRadix, startRadix, h4]
    _ ≤ 2 ^ (2 * j) * (2 ^ (Nat.log2 n + 2) * 2 ^ (Fintype.card (Option State) + 2)) := by
        gcongr
    _ = 2 ^ (2 * j + Nat.log2 n + Fintype.card (Option State) + 4) := by
        rw [← pow_add, ← pow_add]
        ring_nf

variable (k State) in
/-- **The vertices of round `j` have `O(j + log₂ n)` bits.** -/
theorem vertexWidth_roundRadix_le (n j : ℕ) :
    vertexWidth k (roundRadix State n j) ≤
      Fintype.card (Register k) * (2 * j + Nat.log2 n + Fintype.card (Option State) + 4) + 1 := by
  rw [vertexWidth, Nat.size_le]
  calc vertexBound (k := k) (roundRadix State n j)
      ≤ (2 ^ (2 * j + Nat.log2 n + Fintype.card (Option State) + 4)) ^
          Fintype.card (Register k) := Nat.pow_le_pow_left (roundRadix_le_two_pow n j) _
    _ = 2 ^ (Fintype.card (Register k) * (2 * j + Nat.log2 n + Fintype.card (Option State) + 4)) :=
        by rw [← pow_mul, mul_comm]
    _ < _ := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### Fitting the rounds -/

/-- The initial view fits every radix above the finite tags. -/
theorem fits_init (hB : Fintype.card (Option State) + 1 < B) :
    Fits B (registers (ntm.initView w)) := by
  have hc := (Fintype.equivFin (Option State) (some ntm.q₀)).isLt
  intro i
  cases i with
  | inputPos => change 1 < B; omega
  | control => exact hc.trans (by omega)
  | output | head _ | left _ | right _ => change 0 < B; omega

/-- The start vertex lies below the ambient bound of every radix above the finite tags. -/
theorem startID_lt (hB : Fintype.card (Option State) + 1 < B) :
    startID ntm B < vertexBound (k := k) B := by
  have h := vertexID_lt (fits_init (ntm := ntm) (w := []) hB)
  rwa [vertexID_init] at h

/-- **A space bound fits the late rounds**: every view reachable by a source that visits at most
`S` work cells fits the radix of every round from `4 * S + 1` on. -/
theorem fits_roundRadix_of_runsInSpace {S j : ℕ} (hs : ntm.RunsInSpace w S) (hj : 4 * S + 1 ≤ j)
    {v : FiniteCfg k Bool State} (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    Fits (roundRadix State w.length j) (registers v) := by
  have hc := card_lt_startRadix (State := State) w.length
  have hle := startRadix_le_roundRadix (State := State) w.length j
  refine fits_of_runsInSpace_of_le hs ((le_startRadix w.length).trans hle) (by omega) (by omega)
    ?_ hv
  calc 3 ^ (4 * S + 1) ≤ 4 ^ (4 * S + 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ 4 ^ j := Nat.pow_le_pow_right (by omega) hj
    _ ≤ roundRadix State w.length j := Nat.le_mul_of_pos_right _ (by omega)

end Turing.MultiTapeNTM.ConfigurationGraph
