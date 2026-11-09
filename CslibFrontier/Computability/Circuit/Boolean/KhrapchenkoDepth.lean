/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Yablonskii
import CslibFrontier.Computability.Circuit.Boolean.Spira

/-!
# Formula depth from Khrapchenko's bound

A De Morgan formula with at most `d` AND and OR gates on every path has at most `2 ^ d` leaves
(`leafSize_le_two_pow_depthWith_binaryCost`), so a function all of whose formulas have at least `L`
leaves has formula depth at least `⌈log₂ L⌉`, with negations free
(`clog_le_formulaDepth_of_le_leafSize`). With Khrapchenko's bounds
[Jukna, Section 6.8][Jukna2012], the parity of `n` bits has formula depth at least `⌈log₂ n ^ 2⌉`
(`clog_sq_le_formulaDepth_parity`) [Khrapchenko1971], and the threshold function `Th^n_k` at least
`⌈log₂ k (n + 1 - k)⌉` (`clog_mul_le_formulaDepth_threshold`) [Khrapchenko1971b].

For parity this is tight up to one: Yablonskii's balanced formulas
(`CslibFrontier/Computability/Circuit/Boolean/Yablonskii.lean`) give the upper bound `2 ⌈log₂ n⌉`.
In
particular the parity of
`2 ^ k` bits has formula depth exactly `2 k` (`formulaDepth_parity_two_pow`), and for
`0 < r ≤ 2 ^ k` the parity of `2 ^ k + r` bits has formula depth `2 k + 1` or `2 k + 2`.

## Main results

* `Cslib.Circuits.Boolean.clog_le_formulaDepth_of_le_leafSize`: a leaf-size lower bound `L` gives
  the formula depth lower bound `⌈log₂ L⌉`.
* `Cslib.Circuits.Boolean.clog_sq_le_formulaDepth_parity`,
  `Cslib.Circuits.Boolean.two_mul_log_le_formulaDepth_parity`: the formula depth of the parity of
  `n` bits is at least `⌈log₂ n ^ 2⌉ ≥ 2 ⌊log₂ n⌋`.
* `Cslib.Circuits.Boolean.formulaDepth_parity_two_pow`: the formula depth of the parity of `2 ^ k`
  bits is `2 k`.
* `Cslib.Circuits.Boolean.two_mul_add_one_le_formulaDepth_parity`,
  `Cslib.Circuits.Boolean.formulaDepth_parity_two_pow_add_le`: for `0 < r ≤ 2 ^ k`, the formula
  depth of the parity of `2 ^ k + r` bits is between `2 k + 1` and `2 k + 2`.
* `Cslib.Circuits.Boolean.clog_mul_le_formulaDepth_threshold`,
  `Cslib.Circuits.Boolean.clog_sq_div_four_le_formulaDepth_majority`: formula depth lower bounds
  for threshold functions and majority.

## References

* [V. M. Khrapchenko, *Method of determining lower bounds for the complexity of
  Π-schemes*][Khrapchenko1971b]
* [V. M. Khrapchenko, *Complexity of the realization of a linear function in the class of
  Π-circuits*][Khrapchenko1971]
* [S. V. Yablonskii, *Realization of a linear function in the class of π-schemes*][Yablonskii1954]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-- If every De Morgan formula for `f` has at least `L` leaves, the formula depth of `f`, with
negations free, is at least `⌈log₂ L⌉`. -/
theorem clog_le_formulaDepth_of_le_leafSize {f : BooleanFunction n} {L : ℕ}
    (h : ∀ F : Formula signature n, F.Computes interpretation f → L ≤ F.leafSize) :
    Nat.clog 2 L ≤ formulaDepth f := by
  obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_le_two_pow_formulaDepth f
  exact Nat.clog_le_of_le_pow ((h F hF).trans hL)

/-! ### Parity -/

/-- The formula depth of the parity of `n` bits, with negations free, is at least
`⌈log₂ n ^ 2⌉`. -/
theorem clog_sq_le_formulaDepth_parity (n : ℕ) : Nat.clog 2 (n ^ 2) ≤ formulaDepth (parity n) :=
  clog_le_formulaDepth_of_le_leafSize fun _ => sq_le_leafSize_of_computes_parity

/-- The formula depth of the parity of `n` bits, with negations free, is at least `2 log₂ n`. -/
theorem two_mul_log_le_formulaDepth_parity (n : ℕ) :
    2 * Nat.log 2 n ≤ formulaDepth (parity n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine le_trans ?_ (clog_sq_le_formulaDepth_parity n)
  refine (Nat.le_log_of_pow_le one_lt_two ?_).trans (Nat.log_le_clog 2 _)
  calc 2 ^ (2 * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ 2 := by rw [mul_comm, pow_mul]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) 2

/-- **The formula depth of parity.** The parity of `2 ^ k` bits has formula depth `2 k`, with
negations free. -/
theorem formulaDepth_parity_two_pow (k : ℕ) : formulaDepth (parity (2 ^ k)) = 2 * k := by
  refine le_antisymm ?_ ?_
  · exact (formulaDepth_parity_le_two_mul_clog _).trans_eq (by rw [Nat.clog_pow 2 k one_lt_two])
  · exact (two_mul_log_le_formulaDepth_parity _).trans_eq' (by rw [Nat.log_pow one_lt_two])

/-- For `r > 0`, the parity of `2 ^ k + r` bits has formula depth at least `2 k + 1`. -/
theorem two_mul_add_one_le_formulaDepth_parity {k r : ℕ} (hr : 0 < r) :
    2 * k + 1 ≤ formulaDepth (parity (2 ^ k + r)) := by
  refine le_trans ?_ (clog_sq_le_formulaDepth_parity _)
  refine (Nat.lt_clog_iff_pow_lt one_lt_two).2 ?_
  calc 2 ^ (2 * k) = (2 ^ k) ^ 2 := by rw [mul_comm, pow_mul]
    _ < (2 ^ k + r) ^ 2 := Nat.pow_lt_pow_left (by omega) two_ne_zero

/-- For `r ≤ 2 ^ k`, the parity of `2 ^ k + r` bits has formula depth at most `2 k + 2`. -/
theorem formulaDepth_parity_two_pow_add_le {k r : ℕ} (hr : r ≤ 2 ^ k) :
    formulaDepth (parity (2 ^ k + r)) ≤ 2 * k + 2 := by
  refine (formulaDepth_parity_le_two_mul_clog _).trans ?_
  have : Nat.clog 2 (2 ^ k + r) ≤ k + 1 := Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  omega

/-! ### Threshold functions -/

/-- The threshold function `Th^n_k` has formula depth at least `⌈log₂ k (n + 1 - k)⌉`, with
negations free. -/
theorem clog_mul_le_formulaDepth_threshold (n k : ℕ) :
    Nat.clog 2 (k * (n + 1 - k)) ≤ formulaDepth (threshold n k) :=
  clog_le_formulaDepth_of_le_leafSize fun _ => mul_le_leafSize_of_computes_threshold

/-- The majority of `n` bits has formula depth at least `⌈log₂ ⌊(n + 1) ^ 2 / 4⌋⌉`, with negations
free. -/
theorem clog_sq_div_four_le_formulaDepth_majority (n : ℕ) :
    Nat.clog 2 ((n + 1) ^ 2 / 4) ≤ formulaDepth (majority n) :=
  clog_le_formulaDepth_of_le_leafSize fun _ => sq_div_four_le_leafSize_of_computes_majority

end Cslib.Circuits.Boolean
