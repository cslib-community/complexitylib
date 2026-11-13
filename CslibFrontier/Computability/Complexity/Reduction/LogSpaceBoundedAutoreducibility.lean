/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LogSpaceAutoreducibility
public import CslibFrontier.Computability.Complexity.Reduction.LogSpaceBoundedTruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Equality
import CslibFrontier.Tactic.LogSpace

/-!
# Bounded disjunctive and conjunctive completeness gives autoreducibility

## Main definitions

* `Cslib.Complexity.activeSelfQuery`: whether an active query equals its input.

## Main results

* `Cslib.Complexity.logSpaceKTruthTableAutoreducible_of_suppression`: suppress all queries on
  inputs whose answer is already determined, retaining the original bound.
* `Cslib.Complexity.LogSpaceKDTTReducible.autoreducible_of_compl`: negate OR unless a self-query
  occurs, in which case reject without queries.
* `Cslib.Complexity.LogSpaceKCTTReducible.autoreducible_of_compl`: negate AND unless a self-query
  occurs, in which case accept without queries.

## Source mapping

[GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047, 18 March 2013,
Proposition 2.7(2,3), printed page 5 (PDF index 4), asserts that for every complement-closed
class and every `k ≥ 1`, logspace `k`-dtt/`k`-ctt completeness implies logspace `k`-tt
autoreducibility. The class corollaries below use `CompleteUnder`, including membership and
hardness for every encoded problem. On bit words with `encBits` these are the paper's languages;
other injective encodings follow the existing library convention. Count is unary, query input
uses `encPair encA encUnary`, and the evaluator uses `encPair encA encBits` and `encBool`.

Our bounds mean **at most** `k`, and also cover `k = 0`. The OR of an empty answer word is
false; its AND is true. We retain the inherited `L` evaluator convention. All queries are
nonadaptive, and only indices below the count are active. Equality is computed on encoded
instances in logspace; no free oracle or query-avoidance premise is added.

Clause (2) uses the paper's proof: a complement witness with a self-query forces nonmembership
by monotonicity of OR. All queries are then suppressed by setting the count to zero. Without
self-queries, negate the OR. Clause (3) follows the paper's route through complement duality
(Propositions 2.5 and 2.6): a conjunctive witness for `Aᶜ` to `A` is a disjunctive witness for
`A` to `Aᶜ`, so `Aᶜ` is autoreducible by clause (2), and `k`-tt autoreducibility is closed under
complement.
Neither the remaining full-paper results nor the additional parity-logspace application is
claimed here.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α} {k : ℕ}

/-- Test only active query indices; unused generator values are irrelevant. -/
@[expose] def activeSelfQuery (encA : α ↪ List Bool) (r : α → ℕ) (q : α × ℕ → α)
    (a : α) : Bool :=
  ((List.range (r a)).map fun i => decide (encA (q (a, i)) = encA a)).any id

/-- The self-query test is exactly equality at an index below the count. -/
@[simp] theorem activeSelfQuery_eq_true {r : α → ℕ} {q : α × ℕ → α} {a : α} :
    activeSelfQuery encA r q a = true ↔ ∃ i < r a, q (a, i) = a := by
  simp [activeSelfQuery, encA.injective.eq_iff]

/-- A bounded family of queries can be checked for self-queries in logarithmic space. -/
theorem activeSelfQuery_logspace {r : α → ℕ} {q : α × ℕ → α}
    (hr : ComputableInLogSpace r encA encUnary)
    (hq : ComputableInLogSpace q (encPair encA encUnary) encA) (hk : ∀ a, r a ≤ k) :
    ComputableInLogSpace (activeSelfQuery encA r q) encA encBool := by
  have henc : ComputableInLogSpace (fun a : α => encA a) encA encBits :=
    ComputableInLogSpace.of_eq fun _ => rfl
  have heq : ComputableInLogSpace
      (fun p : α × ℕ => decide (encA (q p) = encA p.1))
      (encPair encA encUnary) encBool := by fun_prop
  unfold activeSelfQuery
  apply (ComputableInLogSpace.bitsAny id).comp'
  logspace

/-- Suppress all queries when a logspace test determines the answer. Otherwise preserve the
original generator and evaluator. Only active queries in the surviving branch must avoid input. -/
theorem logSpaceKTruthTableAutoreducible_of_suppression
    {r : α → ℕ} {q : α × ℕ → α} {d : α × List Bool → Bool} {c : α → Bool} (b : Bool)
    (hr : ComputableInLogSpace r encA encUnary)
    (hq : ComputableInLogSpace q (encPair encA encUnary) encA)
    (hd : ComputableInLogSpace d (encPair encA encBits) encBool)
    (hc : ComputableInLogSpace c encA encBool) (hk : ∀ a, r a ≤ k)
    (hne : ∀ a i, c a = false → i < r a → q (a, i) ≠ a)
    (hA : ∀ a, a ∈ A ↔
      (if c a then b else d (a, truthTableAnswers (q ⁻¹' A) r a)) = true) :
    LogSpaceKTruthTableAutoreducible k encA A := by
  refine ⟨fun a => if c a then 0 else r a, q, fun p => if c p.1 then b else d p,
    ⟨⟨by fun_prop, hq, by fun_prop, ?_⟩, ?_⟩, ?_⟩
  · intro a
    cases heq : c a <;> simp [heq, hk a]
  · intro a i hi
    cases heq : c a
    · exact hne a i heq (by simpa [heq] using hi)
    · simp [heq] at hi
  · intro a
    rw [hA a]
    cases heq : c a <;> simp [heq, truthTableAnswers]

/-- A bounded disjunctive complement reduction yields query-avoiding `k`-tt autoreducibility. -/
theorem LogSpaceKDTTReducible.autoreducible_of_compl
    (h : LogSpaceKDTTReducible k encA encA Aᶜ A) :
    LogSpaceKTruthTableAutoreducible k encA A := by
  classical
  obtain ⟨r, q, ⟨hr, hq, hk⟩, hA⟩ := h
  apply logSpaceKTruthTableAutoreducible_of_suppression (c := activeSelfQuery encA r q)
    (d := fun p => !p.2.any id) false hr hq (by fun_prop)
    (activeSelfQuery_logspace hr hq hk) hk
  · intro a i hc hi heq
    have : activeSelfQuery encA r q a = true := activeSelfQuery_eq_true.mpr ⟨i, hi, heq⟩
    simp_all
  · intro a
    by_cases hc : activeSelfQuery encA r q a = true
    · obtain ⟨i, hi, heq⟩ := activeSelfQuery_eq_true.mp hc
      have hnot : a ∉ A := by
        intro ha
        have := (hA a).mpr ⟨i, hi, heq.symm ▸ ha⟩
        exact this ha
      simp [hc, hnot]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true']
      rw [truthTableAnswers_eq_map_range]
      simpa using not_congr (hA a)

/-- A bounded conjunctive complement reduction yields query-avoiding `k`-tt autoreducibility,
by duality with the disjunctive case and closure under complement. -/
theorem LogSpaceKCTTReducible.autoreducible_of_compl
    (h : LogSpaceKCTTReducible k encA encA Aᶜ A) :
    LogSpaceKTruthTableAutoreducible k encA A := by
  have hdtt : LogSpaceKDTTReducible k encA encA Aᶜᶜ Aᶜ :=
    dttReducibleBy_iff_cttReducibleBy_compl.mpr (by simp only [compl_compl]; exact h)
  simpa only [compl_compl] using hdtt.autoreducible_of_compl.compl

/-- Proposition 2.7(2): bounded disjunctive completeness in a complement-closed class. -/
theorem logSpaceKTruthTableAutoreducible_of_kdtt_complete
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (h : CompleteUnder (fun enc => LogSpaceKDTTReducible k enc encA) C encA A)
    (hcompl : ∀ {β : Type} (enc : β ↪ List Bool) (B : Set β), B ∈ C enc → Bᶜ ∈ C enc) :
    LogSpaceKTruthTableAutoreducible k encA A :=
  (h.2 encA Aᶜ (hcompl encA A h.1)).autoreducible_of_compl

/-- Proposition 2.7(3): bounded conjunctive completeness in a complement-closed class. -/
theorem logSpaceKTruthTableAutoreducible_of_kctt_complete
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (h : CompleteUnder (fun enc => LogSpaceKCTTReducible k enc encA) C encA A)
    (hcompl : ∀ {β : Type} (enc : β ↪ List Bool) (B : Set β), B ∈ C enc → Bᶜ ∈ C enc) :
    LogSpaceKTruthTableAutoreducible k encA A :=
  (h.2 encA Aᶜ (hcompl encA A h.1)).autoreducible_of_compl

end Cslib.Complexity
