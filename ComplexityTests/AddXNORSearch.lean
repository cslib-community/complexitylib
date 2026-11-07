/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORSearch
public import Mathlib.Logic.Equiv.Defs

/-!
# Exact search clients and a lazy-simulation obstruction

The final section checks a counterexample to the literal `Real` procedure in
[WangLvShenZhang2027], Lemma 10, PDF pp. 25–26. The trace already has a
collision (`BAD`), so it does not challenge the collision-free coupling or
disprove Theorem 8: a repaired simulator and proof could establish that bound.
-/

public section

open Cslib.Cryptanalysis.AddXNOR

example : meetSearch [1#3] [2#3] 5#3 0#3 = some ([false], [false]) := by decide
example : meetSearch ([] : List (BitVec 3)) [] 1#3 0#3 = none := by decide
example : meetSearch ([] : List (BitVec 3)) [] 0#3 0#3 = some ([], []) := by decide
example : meetSearch [0#0] [0#0] 0#0 0#0 ≠ none := by decide
example : meetSearch [0#1, 0#1] [0#1] 0#1 0#1 ≠ none := by decide

example {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m) :
    meetSearch left right s t ≠ none ↔ Solvable (left ++ right) s t :=
  meetSearch_ne_none_iff left right s t

example {m : ℕ} (right : List (BitVec m)) (s t : BitVec m) :
    (recordTrie (forwardRecords [] s)).nodes ≤ m + 1 ∧
      joinVisits (recordTrie (forwardRecords [] s)) (backwardRecords right t) ≤
        2 ^ right.length * (m + 1) := by
  simpa using meetSearch_trie_resources [] right s t

open Cslib.DataStructure in
example : (((BinaryTrie.empty : BinaryTrie ℕ).insert [] 3).insert [false] 7).find [] = some 3 := by
  decide

open Cslib.DataStructure in
example : (((BinaryTrie.empty : BinaryTrie ℕ).insert [true] 3).insert [true] 7).find [true] =
    some 7 := by decide

open Cslib.DataStructure in
example : (((BinaryTrie.empty : BinaryTrie ℕ).insert [true] 3).insert [true] 7).nodes = 2 := by
  decide

namespace AddXNORIdealSimulationObstruction

/-- Word space for q=3, m=5, T=4, inside Theorem 8's parameter range. -/
abbrev W := Fin 32

example : 3 ≤ (3 : ℕ) ∧ max 3 4 ≤ (4 : ℕ) ∧ 4 ≤ 2 ^ (5 - 3) := by decide

/-- The literal fresh draws of `Real`, conditional on s₀=t=0 and x*=000:
first query π₂,₀(0), second π₁,₀(0), third π₃,₀⁻¹(0).
They use distinct, initially empty tables, so each of these draws has all 32
possibilities under the manuscript's common fresh-answer rule. -/
def obstructingDraw : W × W × W := (0, 1, 0)

/-- The relevant exact tuple of fresh draws has strictly positive uniform mass. -/
example : (Fintype.card {d : W × W × W // d = obstructingDraw} : ℚ) /
    Fintype.card (W × W × W) = 1 / 32768 := by
  norm_num [Fintype.card_prod]

/-- After those three draws, f=g=1. The fourth query π₂,₀(1) is
new and closes the chain. The literal forced-answer rule returns 0, although
π₂,₀(0)=0 is already in that same table. No permutation extends this table. -/
theorem forced_closure_not_permutation :
    ¬ ∃ p : Equiv.Perm W, p 0 = 0 ∧ p 1 = 0 := by
  rintro ⟨p, h0, h1⟩
  have h := p.injective (h0.trans h1.symm)
  norm_num at h

/-- In the actual planted experiment, the first three answers above are
impossible, conditional on these public values and planted word. In contrast,
the literal `Real` procedure permits them before forcing an invalid fourth
answer. This exhibits failure of exact distributional simulation (Lemma 10),
not an adversary violating the bound of Theorem 8. -/
theorem planted_trace_impossible (p₁ p₂ p₃ : Equiv.Perm W)
    (hplant : p₃ (p₂ (p₁ 0)) = 0)
    (hfirst : p₂ 0 = 0) (hsecond : p₁ 0 = 1) (hthird : p₃.symm 0 = 0) : False := by
  have hend : p₂ 1 = 0 := by
    have h := congrArg p₃.symm hplant
    simpa [hsecond, hthird] using h
  exact forced_closure_not_permutation ⟨p₂, hfirst, hend⟩

end AddXNORIdealSimulationObstruction
