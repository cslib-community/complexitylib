/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Amplification.Family
public import CslibFrontier.Foundations.Combinatorics.Expander.AffineFamily
import Mathlib.Tactic.IrreducibleDef

/-!
# Fixed amplification parameters for the arithmetic expanders

The arithmetic family has degree `2 * 257 ^ 12` and a uniform spectral bound strictly below one.
The fixed killing rate `2 ^ 324 + 1` suffices to double the value after preprocessing, powering,
and selected composition over the `128`-symbol answer alphabet, up to the gap `2 ^ (-61)`.
Its walk length is `2 ^ 333`. The threshold uses the full denominator of the second-moment
bound, rather than the smaller cutoff `1 / walkLength²`.

Both parameters are concrete natural numbers, with no search or choice in their definitions.
They are irreducible to keep elaboration from evaluating the astronomical finite types built
from them. The construction is asymptotic: these parameters are not intended for practical use.

## Main definitions

* `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.killRate`: the fixed killing rate.
* `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.walkLength`: the fixed walk length.
* `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gap`: the certified soundness gap.

## Main results

* `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gain`: the concrete parameters supply
  enough gain for the shared doubling theorem.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.PCP.ConstraintGraph.Amplification.Arithmetic

open HadamardTester RotationMap

/-- A fixed killing rate large enough for the concrete arithmetic spectral bound. -/
irreducible_def killRate : ℕ := 4 ^ 162 + 1

/-- The walk length required by the powering bound over the fixed answer alphabet. -/
irreducible_def walkLength : ℕ := 2 * 4 ^ 166

/-- A soundness threshold supported by the exact second-moment bound. -/
noncomputable def gap : ℝ := 1 / 2 ^ 61

/-- The concrete soundness gap is positive. -/
theorem gap_pos : 0 < gap := by norm_num [gap]

/-- The concrete soundness gap is at most one. -/
theorem gap_le_one : gap ≤ 1 := by norm_num [gap]

instance : NeZero killRate := ⟨by rw [killRate_def]; exact Nat.succ_ne_zero _⟩

/-- The chosen killing rate is at least two. -/
theorem two_le_killRate : 2 ≤ killRate := by
  norm_num [killRate_def]

/-- The chosen walk length is positive. -/
theorem one_le_walkLength : 1 ≤ walkLength := by
  norm_num [walkLength_def]

/-- The chosen walk length matches the alphabet size and killing rate. -/
theorem walkLength_eq :
    walkLength = 4 * Fintype.card SelectedAlphabet * (killRate - 1) := by
  rw [walkLength_def, killRate_def, card_alphabet_composeSelected]
  norm_num

/-- The concrete killing rate pays for preprocessing and composition with a factor of two left. -/
theorem gain :
    2 ≤ Amplification.gain 840 (Fintype.card SelectedAlphabet)
        (Fintype.card (AffinePlaneFamilyLabel (ZMod 257) 257))
        walkLength killRate (1 - 9 / (400 * (257 : ℝ) ^ 16)) gap := by
  rw [card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm, card_alphabet_composeSelected,
    killRate_def, walkLength_def]
  norm_num [Amplification.gain, retention, gap]

end Cslib.PCP.ConstraintGraph.Amplification.Arithmetic
