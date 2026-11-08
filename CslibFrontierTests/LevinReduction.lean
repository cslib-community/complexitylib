/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Levin

/-!
# Levin reductions

Checked clients of `Cslib.Complexity.NPRelation` and `Cslib.Complexity.LevinReduction`: the SAT
relation has witnesses, the explicit SAT → 3SAT witness maps compute concrete certificates on a
clause of width four (one auxiliary variable), the composed and identity reductions are available,
and a Levin reduction yields the Karp reduction of the languages. The file is a `module`, so it
also checks that `LevinHard` can be introduced and transported by downstream modules.
-/

public section

namespace CslibFrontierTests.LevinReduction

open Cslib.Complexity Cslib.Logic.PL

/-- One clause of width four, `x₀ ∨ x₁ ∨ x₂ ∨ x₃`, which splits into two clauses of width three
with one auxiliary variable. -/
def φ : CNF ℕ := [[(0, true), (1, true), (2, true), (3, true)]]

/-- The assignment making only `x₃` true, listed in order of first occurrence. -/
def w : List Bool := [false, false, false, true]

/-- The SAT certificate obtained by padding `w` is a witness: the relation is inhabited. -/
theorem isWitness_w : SAT.npRelation.IsWitness φ (SAT.padCertificate φ w) := by
  refine SAT.isWitness_npRelation_iff.2 ⟨SAT.length_padCertificate (by decide), by decide⟩

/-- The split formula has variables `x₀, x₁, y, ¬y, x₂, x₃` in order of occurrence, and the
auxiliary variable `y` (which says that one of `x₂, x₃` holds) is set to `true` by the forward
witness map. -/
example : (toThreeSATWitness (φ, SAT.padCertificate φ w)).take 6 =
    [false, false, true, true, false, true] := by
  decide

/-- The forward witness is a 3SAT witness for the split formula. -/
example : ThreeSAT.npRelation.IsWitness (toThreeSAT φ)
    (toThreeSATWitness (φ, SAT.padCertificate φ w)) :=
  isWitness_toThreeSATWitness isWitness_w

/-- The backward map recovers the original assignment from that witness. -/
example : (ofThreeSATWitness (φ, toThreeSATWitness (φ, SAT.padCertificate φ w))).take 4 = w := by
  decide

/-- An unsatisfiable formula has no witnesses, so its image under the instance map has none
either. -/
example : toThreeSAT [[]] ∉ ThreeSAT.npRelation.language := fun h => by
  have h' := (toThreeSATLevinReduction.mem_language_iff [[]]).2 h
  rw [SAT.language_npRelation] at h'
  obtain ⟨σ, hσ⟩ := h'
  simp at hσ

/-- Levin reductions compose with the identity, and give Karp reductions of the languages. -/
example : PolyTimeReducible encCNF encCNF SAT ThreeSAT := by
  simpa only [SAT.language_npRelation, ThreeSAT.language_npRelation] using
    ((LevinReduction.refl _).trans toThreeSATLevinReduction).toPolyTimeReducible

/-- `LevinHard` unfolds in a downstream module: it is introduced from reductions of every NP
relation. -/
example {S : NPRelation encCNF}
    (h : ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (R : NPRelation encA),
      Nonempty (LevinReduction R S)) : LevinHard S :=
  h

/-- Levin-hardness of SAT transfers to 3SAT along the explicit reduction, and gives `NP`-hardness
of `ThreeSAT`. -/
example (h : LevinHard SAT.npRelation) : NPHard encCNF ThreeSAT :=
  ThreeSAT.language_npRelation ▸ (h.trans toThreeSATLevinReduction).npHard

end CslibFrontierTests.LevinReduction
