/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Computability.KleenePost
import CslibFrontier.Foundations.Computability.KleenePostJump

/-! Oracle codes on small examples: a code that applies the oracle and then the successor, the
stage-bounded evaluator failing on a short prefix and on a low stage and succeeding otherwise, the
use principle for a concrete computation, computable sets below every oracle, positive and negative
halting and witness-search cases for the diagonal halting set and one-step extension predicate, and
the Kleene–Post sets, which are Turing incomparable, strictly below the halting jump `∅'`, and not
computable. -/

namespace CslibFrontierTests.KleenePost

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

/-- Only countably many partial functions are reducible to the empty oracle. -/
example : {f | f ≤ᵀ fun _ => Part.none}.Countable :=
  countable_setOf_turingReducible _

/-! ### The Kleene–Post sets -/

/-- Neither Kleene–Post set is computable: a computable set is below every oracle. -/
theorem kleene_post_not_computable :
    ∃ A B : Set ℕ, ¬Computable (A.indicator 1 : ℕ → ℕ) ∧ ¬Computable (B.indicator 1 : ℕ → ℕ) ∧
      ¬(A.indicator 1 : ℕ → ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) := by
  obtain ⟨A, B, hAB, hBA⟩ := kleene_post
  exact ⟨A, B, fun h => hAB h.partrec.turingReducible, fun h => hBA h.partrec.turingReducible,
    hAB⟩

/-- A Kleene–Post degree has countably many predecessors. -/
example : ∃ d₁ d₂ : TuringDegree, ¬d₁ ≤ d₂ ∧ (Set.Iic d₁).Countable := by
  obtain ⟨d₁, d₂, h₁, -⟩ := TuringDegree.exists_incomparable
  exact ⟨d₁, d₂, h₁, d₁.countable_Iic⟩

/-- The Kleene–Post degrees are distinct. -/
example : ∃ d₁ d₂ : TuringDegree, d₁ ≠ d₂ := by
  obtain ⟨d₁, d₂, h, -⟩ := TuringDegree.exists_incomparable
  exact ⟨d₁, d₂, fun e => h (e ▸ le_rfl)⟩

/-! ### Diagonal halting set and witness search -/

/-- The constant-zero and successor partial recursive codes halt on their own Gödel numbers. -/
example : Encodable.encode Nat.Partrec.Code.zero ∈ KleenePost.halting := by
  simp [KleenePost.halting, Nat.Partrec.Code.eval, pure, PFun.pure]

example : Encodable.encode Nat.Partrec.Code.succ ∈ KleenePost.halting := by
  simp [KleenePost.halting, Nat.Partrec.Code.eval]

/-- The unbounded search code `rfind' succ` never finds a zero output and therefore lies outside
the diagonal halting set `halting`. -/
example :
    Encodable.encode (Nat.Partrec.Code.rfind' Nat.Partrec.Code.succ) ∉ KleenePost.halting := by
  intro h
  have hdom : (Nat.rfind fun _ => Part.some false).Dom := by
    simpa [KleenePost.halting, Nat.Partrec.Code.eval] using h
  obtain ⟨_, hn, _⟩ := Nat.rfind_dom.mp hdom
  simp at hn

/-- `Code.primrec_evaln` certifies primitive recursiveness of stage-bounded evaluation in the
oracle prefix. -/
example : Primrec (fun σ : List ℕ => evaln σ 2 succOracle 1) :=
  Code.primrec_evaln.comp (Primrec.id.pair ((Primrec.const (2, succOracle)).pair (Primrec.const 1)))

/-- Positive witness-search case: extending `[false]` to `[false, true]` at stage `3` makes
`succOracle` output `2` on input `1`. -/
theorem haltsPred_succOracle_pos :
    KleenePost.haltsPred succOracle [false] 1
      (Encodable.encode (([false, true] : List Bool), 3, 2)) :=
  ⟨([false, true], 3, 2), Encodable.encodek _, ⟨[true], rfl⟩, by
    simp [KleenePost.bits, evaln, succOracle]⟩

/-- Negative witness-search case: the prefix `[false]` is too short for `succOracle` on input `1`
at stage `2`. -/
theorem not_haltsPred_succOracle_short :
    ¬KleenePost.haltsPred succOracle [false] 1
      (Encodable.encode (([false] : List Bool), 2, 1)) := by
  rintro ⟨p, hp, _, heval⟩
  rw [Encodable.encodek] at hp
  injection hp with h_eq
  subst h_eq
  simp [KleenePost.bits, evaln, succOracle] at heval

/-- An oracle code `rfind' succ` that never halts under any finite oracle prefix. -/
theorem evaln_rfind_succ_eq_none (σ : List ℕ) :
    ∀ k x, evaln σ k (Code.rfind' Code.succ) x = none
  | 0, _ => by simp [evaln]
  | k + 1, x => by
    simp only [evaln, Nat.unpaired, Nat.pair_unpair, Option.bind_eq_bind]
    by_cases hx : x ≤ k
    · simp [hx, evaln_rfind_succ_eq_none σ k]
    · simp [hx]

/-- `rfind' succ` has no halting extension above any prefix `τ` and input `x`. -/
theorem not_halts_rfind_succ (τ : List Bool) (x : ℕ) :
    ¬KleenePost.Halts (Code.rfind' Code.succ) τ x := by
  rintro ⟨p, _, heval⟩
  rw [evaln_rfind_succ_eq_none] at heval
  exact Option.not_mem_none _ heval

/-- The primitive-recursive reduction `halts_reducibleTo_halting` maps a halting instance into
`halting` and a non-halting instance outside `halting`. -/
example :
    ∃ K : (Code × List Bool × ℕ) → ℕ,
      Primrec K ∧
      K (succOracle, [false], 1) ∈ KleenePost.halting ∧
      K (Code.rfind' Code.succ, [], 0) ∉ KleenePost.halting := by
  obtain ⟨K, hK, hred⟩ := KleenePost.halts_reducibleTo_halting
  refine ⟨K, hK, (hred succOracle [false] 1).mp ?_,
    fun hmem => not_halts_rfind_succ [] 0 ((hred (Code.rfind' Code.succ) [] 0).mpr hmem)⟩
  exact (KleenePost.Halts_iff_exists_haltsPred succOracle [false] 1).mpr
    ⟨_, haltsPred_succOracle_pos⟩

/-! ### Combined Kleene–Post incomparability and below-jump bound -/

/-- The same two sets `A` and `B` constructed by Kleene–Post are simultaneously Turing
incomparable and Turing reducible to the halting set `halting` (`∅'`). -/
theorem kleene_post_incomparable_below_jump :
    ∃ A B : Set ℕ,
      ¬(A.indicator 1 : ℕ → ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) ∧
      ¬(B.indicator 1 : ℕ → ℕ) ≤ᵀ (A.indicator 1 : ℕ → ℕ) ∧
      (A.indicator 1 : ℕ → ℕ) ≤ᵀ (KleenePost.halting.indicator 1 : ℕ → ℕ) ∧
      (B.indicator 1 : ℕ → ℕ) ≤ᵀ (KleenePost.halting.indicator 1 : ℕ → ℕ) := by
  refine ⟨{n | KleenePost.limA n = true}, {n | KleenePost.limB n = true}, ?_⟩
  rw [KleenePost.indicator_eq, KleenePost.indicator_eq]
  exact ⟨KleenePost.not_limA_le_limB, KleenePost.not_limB_le_limA,
    kleene_post_below_jump.1, kleene_post_below_jump.2⟩

/-- In `TuringDegree`, the two Kleene–Post degrees are incomparable and strictly below the degree
of the halting set `∅'`. -/
theorem exists_incomparable_lt_jump :
    let dJump : TuringDegree :=
      toAntisymmetrization _ (KleenePost.halting.indicator 1 : ℕ → ℕ)
    ∃ d₁ d₂ : TuringDegree, ¬d₁ ≤ d₂ ∧ ¬d₂ ≤ d₁ ∧ d₁ < dJump ∧ d₂ < dJump := by
  intro dJump
  obtain ⟨A, B, hAB, hBA, hAJ, hBJ⟩ := kleene_post_incomparable_below_jump
  refine ⟨toAntisymmetrization _ (A.indicator 1 : ℕ → ℕ),
    toAntisymmetrization _ (B.indicator 1 : ℕ → ℕ), hAB, hBA,
    lt_of_le_not_ge hAJ (fun hJA => hBA (TuringReducible.trans hBJ hJA)),
    lt_of_le_not_ge hBJ (fun hJB => hAB (TuringReducible.trans hAJ hJB))⟩

end CslibFrontierTests.KleenePost
