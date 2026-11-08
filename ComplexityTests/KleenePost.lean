/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Computability.KleenePost

/-! Oracle codes on small examples: a code that applies the oracle and then the successor, the
stage-bounded evaluator failing on a short prefix and on a low stage and succeeding otherwise, the
use principle for a concrete computation, computable sets below every oracle, and the Kleene–Post
sets, which are not computable and lie in distinct Turing degrees. -/

namespace ComplexityTests.KleenePost

open Nat.RecursiveIn Nat.RecursiveIn.Code
open scoped Computability

/-! ### A concrete oracle code -/

/-- Query the oracle and add one. -/
def succOracle : Code := comp succ oracle

theorem eval_succOracle (g : ℕ →. ℕ) (n : ℕ) : eval g succOracle n = (g n).map Nat.succ :=
  Part.bind_some_eq_map _ _

/-- The successor of an oracle is Turing reducible to the oracle, with `succOracle` as witness. -/
theorem succ_oracle_le (g : ℕ →. ℕ) : (fun n => (g n).map Nat.succ) ≤ᵀ g :=
  turingReducible_iff_exists_code.2 ⟨succOracle, funext (eval_succOracle g)⟩

/-! ### Stage-bounded evaluation -/

/-- With the prefix `[7, 3]` and stage `2`, the oracle query at `1` returns `3`. -/
example : evaln [7, 3] 2 oracle 1 = some 3 := by
  simp [evaln]

/-- The prefix `[7]` is too short for the query at `1`. -/
example : evaln [7] 2 oracle 1 = none := by
  simp [evaln]

/-- Stage `1` is too low for the input `1`, whatever the prefix. -/
example : evaln [7, 3] 1 oracle 1 = none := by
  simp [evaln]

/-- `succOracle` against `[0, 1]` at stage `2` and input `1` returns `2`. -/
example : evaln [0, 1] 2 succOracle 1 = some 2 := by
  simp [evaln, succOracle]

/-- Intermediate values are also bounded by the stage: against `[7, 3]` the oracle answer `3` is
too large for the successor step at stage `2`, and stage `4` suffices. -/
example : evaln [7, 3] 2 succOracle 1 = none ∧ evaln [7, 3] 4 succOracle 1 = some 4 := by
  simp [evaln, succOracle]

/-- A stage-`2` computation ignores everything after the first two oracle values. -/
example : evaln [0, 1, 9, 9] 2 succOracle 1 = evaln [0, 1] 2 succOracle 1 :=
  (evaln_take [0, 1, 9, 9] 2 succOracle 1).symm

/-- The stage-bounded result is a value of the full evaluation for any oracle extending the
prefix, here the identity. -/
example : 2 ∈ eval ((id : ℕ → ℕ) : ℕ →. ℕ) succOracle 1 := by
  refine evaln_sound (σ := [0, 1]) (k := 2) (fun i hi => ?_) (by simp [evaln, succOracle])
  obtain _ | _ | i := i
  · exact Part.mem_some _
  · exact Part.mem_some _
  · exact absurd hi (by simp)

/-! ### The use principle -/

/-- `succOracle` at input `5` relative to the identity oracle converges to `6`, and the same
holds for every total oracle agreeing with the identity below some bound. -/
example : ∃ N, ∀ g : ℕ → ℕ, (∀ i < N, g i = i) →
    6 ∈ eval (g : ℕ →. ℕ) succOracle 5 :=
  exists_use (f := id) (by simp [eval_succOracle])

/-! ### Computable sets lie below every oracle -/

/-- The set of even numbers. -/
def evens : Set ℕ := {n | Even n}

theorem evens_indicator_eq : (evens.indicator 1 : ℕ → ℕ) = fun n => if n % 2 = 0 then 1 else 0 := by
  funext n
  by_cases h : n % 2 = 0 <;> simp [evens, Set.indicator, Nat.even_iff, h]

theorem evens_le (g : ℕ →. ℕ) : (evens.indicator 1 : ℕ → ℕ) ≤ᵀ g := by
  rw [evens_indicator_eq]
  refine Partrec.turingReducible (Computable.partrec ?_)
  exact (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
    (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)).to_comp

/-- Only countably many partial functions are reducible to the empty oracle, and the Kleene–Post
degrees have countably many predecessors. -/
example : {f | f ≤ᵀ fun _ => Part.none}.Countable :=
  countable_setOf_turingReducible _

/-! ### The Kleene–Post sets -/

/-- Neither Kleene–Post set is computable: a computable set is below every oracle. -/
theorem kleene_post_not_partrec :
    ∃ A B : Set ℕ, ¬Computable (A.indicator 1 : ℕ → ℕ) ∧ ¬Computable (B.indicator 1 : ℕ → ℕ) ∧
      ¬(A.indicator 1 : ℕ → ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) := by
  obtain ⟨A, B, hAB, hBA⟩ := kleene_post
  exact ⟨A, B, fun h => hAB h.partrec.turingReducible, fun h => hBA h.partrec.turingReducible,
    hAB⟩

/-- The Kleene–Post degrees are distinct. -/
example : ∃ d₁ d₂ : TuringDegree, d₁ ≠ d₂ := by
  obtain ⟨d₁, d₂, h, -⟩ := TuringDegree.exists_incomparable
  exact ⟨d₁, d₂, fun e => h (e ▸ le_rfl)⟩

end ComplexityTests.KleenePost
