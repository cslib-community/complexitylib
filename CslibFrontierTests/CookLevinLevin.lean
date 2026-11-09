/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.CookLevin.Levin

/-!
# Every NP relation Levin-reduces to 3SAT

Checked clients of `Cslib.Complexity.CookLevin.ThreeSAT_levinHard` in a downstream module: a
Levin reduction of an arbitrary NP relation to 3SAT is obtained and used to move a witness of the
original relation to a 3SAT witness of the reduced formula, and the Karp hardness of `ThreeSAT` is
recovered from it.
-/

public section

namespace CslibFrontierTests.CookLevinLevin

open Cslib.Complexity Cslib.Logic.PL

/-- A witness of any NP relation is carried to a 3SAT witness of the reduced instance, and a
3SAT witness of the reduced instance is carried back. -/
example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) {a : α} {w : List Bool}
    (h : R.IsWitness a w) :
    ∃ r : LevinReduction R ThreeSAT.npRelation,
      ThreeSAT.npRelation.IsWitness (r.toFun a) (r.forwardWitness (a, w)) ∧
        R.IsWitness a (r.backwardWitness (a, r.forwardWitness (a, w))) := by
  obtain ⟨r⟩ := CookLevin.ThreeSAT_levinHard enc R
  have hf := r.isWitness_forwardWitness a w h
  exact ⟨r, hf, r.isWitness_backwardWitness a _ hf⟩

/-- The relation of SAT itself Levin-reduces to 3SAT through Cook–Levin; the composite instance map
is polynomial-time. -/
example : Nonempty (LevinReduction SAT.npRelation ThreeSAT.npRelation) :=
  CookLevin.ThreeSAT_levinHard encCNF SAT.npRelation

/-- The Karp hardness of `ThreeSAT` follows from its Levin hardness. -/
example : NPHard encCNF ThreeSAT :=
  ThreeSAT.language_npRelation ▸ CookLevin.ThreeSAT_levinHard.npHard

/-- The forward witness of the Cook–Levin reduction has the length that the SAT relation
prescribes for the reduced formula. -/
example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) {k : ℕ} {State : Type}
    [Fintype State] [DecidableEq State] (tm : Turing.MultiTapeTM k Bool State) (c d : ℕ)
    (hrun : CookLevin.RunsVerifier R tm c d) {a : α} {w : List Bool} (h : R.IsWitness a w) :
    (CookLevin.forwardWitness tm R.certLength c d enc (a, w)).length =
      (encCNF (CookLevin.reduce tm R.certLength c d enc a)).length :=
  (SAT.isWitness_npRelation_iff.1 (CookLevin.isWitness_forwardWitness hrun h)).1

/-- `RunsVerifier` is constructed in a downstream module, from the machine behind the verifier's
polynomial-time certificate, exactly as `CookLevin.SAT_levinHard` does. -/
example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) :
    ∃ (k : ℕ) (State : Type) (tm : Turing.MultiTapeTM k Bool State) (c d : ℕ),
      Finite State ∧ CookLevin.RunsVerifier R tm c d := by
  obtain ⟨t, _, ht, -, k, State, hfin, tm, htm⟩ := R.computableInPolyTime_verifier
  obtain ⟨c, d, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  exact ⟨k, State, tm, c, d, hfin, fun a w _ => (htm (a, w)).runFrom_of_le (ht _)⟩

end CslibFrontierTests.CookLevinLevin
