/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of CslibFrontier.Computability.Kolmogorov.MINKTStar.Generator)

public import CslibFrontier.Computability.Kolmogorov.MINKTStar.Generator
import CslibFrontier.Computability.Complexity.Problems.CMMSA.Size

/-! # Tests for the `MINKT*` generator of the CMMSA table -/

public section

namespace CslibFrontierTests.KolmogorovMINKTStarGenerator

open Cslib Cslib.Complexity Cslib.Kolmogorov Cslib.Kolmogorov.MINKTStar Cslib.PartialMCSP.FromCMMSA

/-- How a reduction uses the generator: a Yes instance gives a witness for `I` and `λ` whose
printed table has the length of the CMMSA table and whose encoding is at most `sizeBound`. -/
example {Δ k lam : ℕ} {g σ : ℝ} {I : CMMSAInstance} (hI : I ∈ (GapCMMSA Δ g σ).yes)
    (hlam : 1 ≤ lam) (f : VarFunctions I lam) :
    ∃ w : GenWitness, (w.generate Δ k).length = 2 ^ inputLength I Δ k lam ∧
      (GenWitness.enc w).length ≤ GenWitness.sizeBound Δ I lam := by
  obtain ⟨w, rfl, rfl, -, hsize⟩ := GenWitness.exists_consistent_generate Δ k hI hlam f
  exact ⟨w, GenWitness.length_generate Δ k w, hsize⟩

/-- The size bound unfolds to `(4 Δ + 3) |enc I| + 3 + (4 θ + 2) λ`. -/
example (I : CMMSAInstance) (lam : ℕ) :
    GenWitness.sizeBound 1 I lam =
      7 * (CMMSAInstance.encoding I).length + 3 + (4 * I.threshold + 2) * lam :=
  rfl

/-! The formula `x₀ ∨ x₁` over two variables of weight `2`, at threshold `2`, with `Δ = 2` and
`k = λ = 1`; `S = {0}` satisfies it. There is one formula, so the index takes no bits; each slot
holds a `1`-bit seed and a mask, so inputs have `2 · 2 · 2 = 8` bits. The witness lists the table of
`x₀` only and prints the parity of the first term. Where the table is defined, both terms have its
parity, so the printed table agrees with the table computed from both variables' tables. -/

/-- The formula `x₀ ∨ x₁` over two variables of weight `2`, at threshold `2`. -/
def orInst : CMMSAInstance := ⟨[2, 2], 2, [[[(0, true)], [(1, true)]]]⟩

example : inputLength orInst 2 1 1 = 8 := by decide

/-- The honest witness for `S = {0}`: the first term, and the table of `x₀ = id` only. -/
def witness : GenWitness := ⟨orInst, 1, [0], [[false, true], []]⟩

example : (witness.generate 2 1).length = 256 := by decide +kernel

/-- At the defined entries of the CMMSA table for `x₀ = x₁ = id`, computed from both tables, the
printed table agrees. -/
example : ∀ i : Fin 256,
    ∀ b, entryN orInst 2 1 1 [[false, true], [false, true]] i = some b →
      GenWitness.genEntry 2 1 witness i = b := by
  decide +kernel

/-- Half of the entries are defined, so the agreement is not vacuous. -/
example : ((List.range 256).filterMap
    (entryN orInst 2 1 1 [[false, true], [false, true]])).length = 128 := by
  decide +kernel

/-- The tables matter: choosing the second term but listing only the table of `x₀` prints a table
that disagrees with some defined entry. -/
example : ¬ ∀ i : Fin 256,
    ∀ b, entryN orInst 2 1 1 [[false, true], [false, true]] i = some b →
      GenWitness.genEntry 2 1 ⟨orInst, 1, [1], [[false, true], []]⟩ i = b := by
  decide +kernel

end CslibFrontierTests.KolmogorovMINKTStarGenerator
