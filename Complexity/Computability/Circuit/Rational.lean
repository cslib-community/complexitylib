/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.MatrixEval
public import Complexity.Computability.Circuit.Rational.Executable

/-!
# Rational hitting lists, nonzeroness, and admissibility

A noncommutative rational formula is *nonzero* if it has a defined nonzero value at some
substitution of square rational matrices of positive dimension, and *admissible* if it is defined
at some such substitution. For all `n` and `s` there is an explicit, executable list of
substitutions of rational matrices, of dimension and encoding length polynomial in `n + s`, at
which every admissible nonzero formula in `n` variables with at most `s` nodes takes an invertible
value somewhere (`hittingList_hits`). The construction is OpenAI's.

The list yields executable tests for nonzeroness and admissibility, by exact rational matrix
evaluation. The admissibility test needs a list for two extra syntax nodes: if `f` has a defined
value, either `f` or `f + 1` has a nonzero value. The correctness theorems do not assert
polynomial bit complexity of formula evaluation. The tests are deductions from the source result,
without a claim of new priority. The generator's running time is bounded in
`Complexity.Computability.Circuit.Rational.Runtime`: `Cslib.Circuits.Rational.hittingList_polytime`
computes the encoding `encodeOutput (hittingList n s)` tidily in polynomial time from unary
`(n, s)`.

## Main definitions

* `Cslib.Circuits.Rational.hittingList`: the list of matrix substitutions for `n` variables and
  `s` nodes.
* `Cslib.Circuits.Rational.Formula.admissible?`, `Cslib.Circuits.Rational.Formula.nonzero?`:
  the executable tests.

## Main results

* `Cslib.Circuits.Rational.hittingList_hits`: the list hits every admissible nonzero formula with
  at most `s` nodes; for `s = 0` this is `Cslib.Circuits.Rational.hits_zero`.
* `Cslib.Circuits.Rational.hittingList_dimension_le`,
  `Cslib.Circuits.Rational.hittingList_encoding_length_le`: polynomial bounds on the dimension and
  on the length of the binary encoding.
* `Cslib.Circuits.Rational.admissible_inv_iff_nonzero`: the inverse of a formula is admissible
  exactly when the formula is nonzero.
* `Cslib.Circuits.Rational.Admissible.exists_dimension_le`: an admissible formula has a witness of
  polynomially bounded dimension.
* `Cslib.Circuits.Rational.Formula.admissible?_eq_true_iff`,
  `Cslib.Circuits.Rational.Formula.nonzero?_eq_true_iff`: the tests are correct, so admissibility
  and nonzeroness are decidable.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Main.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

/-- The explicit, executable list of rational matrix substitutions. -/
def hittingList (n s : ℕ) : Output n := ExecutableGenerator.list n s

/-- Every list hits the formulas with at most `0` nodes, since every formula has a node. -/
theorem hits_zero {n : ℕ} (H : Output n) : Hits 0 H := fun f hf =>
  absurd hf (Nat.not_le_of_gt f.nodeCount_pos)

/-- The generated list hits every admissible nonzero formula with at most `s` nodes at an invertible
value. This holds for all `n` and `s`; for `s = 0` it is `hits_zero`. -/
theorem hittingList_hits (n s : ℕ) : Hits s (hittingList n s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact hits_zero _
  · rw [hittingList, ExecutableGenerator.list_spec]
    exact Generator.list_hits n s hs

/-- The generated matrices have polynomially bounded dimension. -/
theorem hittingList_dimension_le (n s : ℕ) :
    (hittingList n s).dimension ≤ 256 * (n + s + 1) ^ 10 := by
  rw [hittingList, ExecutableGenerator.list_spec]
  exact Generator.list_dimension_bound n s

/-- The complete reduced-rational binary encoding has polynomial length, for all `n` and `s`,
including `n = 0`. The constant `PolynomialBounds.outputConstant` differs from the source's, which
assumes `1 ≤ n`: covering `n = 0` raises the grid-size coefficient from `24577` to `49153`. -/
theorem hittingList_encoding_length_le (n s : ℕ) :
    (encodeOutput (hittingList n s)).length ≤
      PolynomialBounds.outputConstant * (n + s + 1) ^ 104 := by
  rw [hittingList, ExecutableGenerator.list_spec]
  exact Generator.list_output_bound n s

/-- Some matrix evaluation of the inverse is defined exactly when the formula is nonzero. -/
theorem admissible_inv_iff_nonzero {n : ℕ} (f : Formula n) :
    Admissible (.inv f) ↔ Nonzero f :=
  (hittingList_hits n f.nodeCount).admissible_inv_iff_nonzero f le_rfl

/-- Every nonempty matrix domain has a witness of polynomially bounded dimension. -/
theorem Admissible.exists_dimension_le {n : ℕ} {f : Formula n} (hf : Admissible f) :
    ∃ d, 0 < d ∧ d ≤ 256 * (n + f.nodeCount + 3) ^ 10 ∧
      ∃ (X : Tuple n d) (v : Mat d), Evaluates f X v := by
  obtain ⟨X, _, v, he⟩ :=
    ((hittingList_hits n (f.nodeCount + 2)).admissible_iff f le_rfl).mp hf
  refine ⟨_, (hittingList n (f.nodeCount + 2)).dimension_pos, ?_, X, v, he⟩
  simpa only [Nat.add_assoc] using hittingList_dimension_le n (f.nodeCount + 2)

/-- Test whether the formula has a defined positive-dimensional rational matrix evaluation, by
exact evaluation on the hitting list for `f.nodeCount + 2` nodes: the two extra nodes cover
`f + 1`, which is nonzero wherever `f` is defined and zero. -/
def Formula.admissible? {n : ℕ} (f : Formula n) : Bool :=
  (hittingList n (f.nodeCount + 2)).admissibilityTest f

/-- Test whether the formula has a defined nonzero rational matrix evaluation, by searching the
hitting list for `f.nodeCount + 2` nodes for an invertible value. A list for `f.nodeCount` nodes
would suffice for this test; the same list as for `Formula.admissible?` is used. -/
def Formula.nonzero? {n : ℕ} (f : Formula n) : Bool :=
  (hittingList n (f.nodeCount + 2)).nonzeroTest f

/-- The generated finite domain test is correct, with no promise on the formula. It uses that the
list hits formulas with `f.nodeCount + 2` nodes. -/
theorem Formula.admissible?_eq_true_iff {n : ℕ} (f : Formula n) :
    f.admissible? = true ↔ Admissible f :=
  (hittingList_hits n (f.nodeCount + 2)).admissibilityTest_eq_true_iff f le_rfl

/-- The generated finite nonzeroness test is correct, with no admissibility promise. It uses only
that the list hits formulas with `f.nodeCount` nodes. -/
theorem Formula.nonzero?_eq_true_iff {n : ℕ} (f : Formula n) :
    f.nonzero? = true ↔ Nonzero f :=
  (hittingList_hits n (f.nodeCount + 2)).nonzeroTest_eq_true_iff f (by lia)

/-- Computed decidability of the existence of a defined matrix evaluation. -/
instance decidableAdmissible {n : ℕ} (f : Formula n) : Decidable (Admissible f) :=
  decidable_of_iff (f.admissible? = true) f.admissible?_eq_true_iff

/-- Computed decidability of the existence of a defined nonzero matrix evaluation. -/
instance decidableNonzero {n : ℕ} (f : Formula n) : Decidable (Nonzero f) :=
  decidable_of_iff (f.nonzero? = true) f.nonzero?_eq_true_iff

end Cslib.Circuits.Rational
