/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LogSpaceAutoreducibility
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Lex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Tactic.LogSpace
import Mathlib.Data.List.Shortlex

/-!
# Local logspace self-reducibility

## Source mapping

Definitions 3.1 and 3.2 of [GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC
TR13-047, 18 March 2013, printed page 6 (PDF index 5). An active query has exactly the
input's encoded length, is strictly lexicographically smaller (false before true), and agrees
on the prefix before the last $\lceil\log_2 n\rceil$ bits. `Nat.clog 2` also gives the
source convention $\log 0=0$. On words with `encBits` these are the literal source conditions;
on other instance types they apply to the explicit injective encoding, not the abstract value.
Only active indices are constrained. Zero queries are allowed, including at minimal suffixes.

The resource and answer conventions are exactly those of `LogSpaceTruthTableReducible`:
unary count and index, encoded queries, and an `L` evaluator on the input and answer word.
The disjunctive/conjunctive definitions explicitly allow either Boolean base answer at zero
queries; they do not force the empty OR/AND answer. The base bit is logspace computable.
The indexed presentation replaces the source's tagged bit-or-nonempty-list output; no
machine equivalence with a serialized tagged-list convention is asserted here.

This is a definition and semantic milestone, **not Lemma 3.3(1)**. The unary dependency below
is mathematical semantics with fixed off-input answers, not a free oracle machine or a
resource certificate. Native regeneration of virtual query inputs and oracle answers during
unbounded evaluation, followed by the source's Proposition 2.1 conversion, remains unproved.
Concrete NL/P complete instances, Theorem 3.5, and Sections 4–5 remain open.

## Main definitions

* `Cslib.Complexity.LocalSelfReductionQuery`: the exact three word conditions.
* `Cslib.Complexity.LogSpaceTruthTableSelfReducible`: local indexed tt self-reducibility.
* `Cslib.Complexity.LogSpaceDTTSelfReducible`: local OR self-reducibility with base answers.
* `Cslib.Complexity.LogSpaceCTTSelfReducible`: local AND self-reducibility with base answers.
* `Cslib.Complexity.truthTableUnaryDependency`: the function $h_x^q$ in Lemma 3.3's proof.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A permitted query word, with the paper's ceiling-logarithm suffix window. -/
@[expose] def LocalSelfReductionQuery (x y : List Bool) : Prop :=
  y.length = x.length ∧ List.Lex (· < ·) y x ∧
    y.take (x.length - Nat.clog 2 x.length) = x.take (x.length - Nat.clog 2 x.length)

instance (x y : List Bool) : Decidable (LocalSelfReductionQuery x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Strict lexicographic descent forbids a self-query. -/
theorem LocalSelfReductionQuery.ne {x y : List Bool} (h : LocalSelfReductionQuery x y) :
    y ≠ x := by
  intro heq
  have hlex := h.2.1
  rw [heq] at hlex
  exact List.lex_irrefl (fun b => lt_irrefl b) x hlex

/-- Consecutive permitted queries stay within the original suffix window. -/
theorem LocalSelfReductionQuery.trans {x y z : List Bool}
    (hxy : LocalSelfReductionQuery x y) (hyz : LocalSelfReductionQuery y z) :
    LocalSelfReductionQuery x z := by
  refine ⟨hyz.1.trans hxy.1, List.lex_trans (fun h₁ h₂ => lt_trans h₁ h₂) hyz.2.1 hxy.2.1, ?_⟩
  have hp := hyz.2.2
  rw [hxy.1] at hp
  exact hp.trans hxy.2.2

/-- Strict local descent terminates. Equal lengths are essential: unrestricted lexicographic
order on finite words is not well-founded. This supplies semantic termination only. -/
theorem localSelfReductionQuery_wellFounded :
    WellFounded (fun y x => LocalSelfReductionQuery x y) := by
  have hb : WellFounded (fun a b : Bool => a < b) :=
    (measure Bool.toNat).wf.mono fun a b h => by
      obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp h
      exact (by decide : 0 < 1)
  exact (List.Shortlex.wf hb).mono fun _ _ h => List.Shortlex.of_lex h.1 h.2.1

/-- Locality permits storing just the suffix and regenerating the common prefix.
This is a word identity, not a space bound for a machine implementing regeneration. -/
theorem LocalSelfReductionQuery.reconstruct {x y : List Bool}
    (h : LocalSelfReductionQuery x y) :
    y = x.take (x.length - Nat.clog 2 x.length) ++
      y.drop (x.length - Nat.clog 2 x.length) := by
  rw [← h.2.2, List.take_append_drop]

/-- The variable suffix has at most the paper's ceiling-logarithm length. -/
theorem LocalSelfReductionQuery.suffix_length {x y : List Bool}
    (h : LocalSelfReductionQuery x y) :
    (y.drop (x.length - Nat.clog 2 x.length)).length ≤ Nat.clog 2 x.length := by
  rw [List.length_drop, h.1]
  omega

variable {α β : Type} {encA : α ↪ List Bool} {A : Set α}

/-- Definition 3.1, tt clause, using the existing native indexed reduction contract. -/
@[expose] def LogSpaceTruthTableSelfReducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encA ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    (∀ a i, i < r a → LocalSelfReductionQuery (encA a) (encA (q (a, i)))) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' A) r a) = true

/-- Every local tt self-reduction is a query-avoiding tt autoreduction. -/
theorem LogSpaceTruthTableSelfReducible.logSpaceTruthTableAutoreducible
    (h : LogSpaceTruthTableSelfReducible encA A) :
    LogSpaceTruthTableAutoreducible encA A := by
  obtain ⟨r, q, d, hr, hq, hd, hlocal, hA⟩ := h
  exact ⟨r, q, d, hr, hq, hd, fun a i hi heq => (hlocal a i hi).ne (congrArg encA heq), hA⟩

/-- Every language already in `L` has a zero-query local self-reduction.
The unused query generator is identity and is deliberately not constrained. -/
theorem LogSpaceTruthTableSelfReducible.of_mem_L (h : A ∈ L encA) :
    LogSpaceTruthTableSelfReducible encA A := by
  obtain ⟨d, hd, hA⟩ := h
  exact ⟨fun _ => 0, Prod.fst, fun p => d p.1,
    ComputableInLogSpace.const 0, by fun_prop, by fun_prop,
    fun _ _ hi => (Nat.not_lt_zero _ hi).elim, fun a => hA a⟩

/-- Definition 3.2's disjunctive clause, including either zero-query base answer. -/
@[expose] def LogSpaceDTTSelfReducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (base : α → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encA ∧
    ComputableInLogSpace base encA encBool ∧
    (∀ a i, i < r a → LocalSelfReductionQuery (encA a) (encA (q (a, i)))) ∧
    ∀ a, a ∈ A ↔ if r a = 0 then base a = true else ∃ i < r a, q (a, i) ∈ A

/-- Definition 3.2's conjunctive clause, including either zero-query base answer. -/
@[expose] def LogSpaceCTTSelfReducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (base : α → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encA ∧
    ComputableInLogSpace base encA encBool ∧
    (∀ a i, i < r a → LocalSelfReductionQuery (encA a) (encA (q (a, i)))) ∧
    ∀ a, a ∈ A ↔ if r a = 0 then base a = true else ∀ i < r a, q (a, i) ∈ A

/-- An OR self-reduction with explicit base answers is an ordinary tt self-reduction. -/
theorem LogSpaceDTTSelfReducible.logSpaceTruthTableSelfReducible
    (h : LogSpaceDTTSelfReducible encA A) : LogSpaceTruthTableSelfReducible encA A := by
  obtain ⟨r, q, base, hr, hq, hb, hlocal, hA⟩ := h
  refine ⟨r, q, fun p => if r p.1 = 0 then base p.1 else p.2.any id,
    hr, hq, by fun_prop, hlocal, fun a => ?_⟩
  classical
  rw [hA a]
  by_cases hz : r a = 0
  · simp [hz]
  · simp [hz, truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]

/-- An AND self-reduction with explicit base answers is an ordinary tt self-reduction. -/
theorem LogSpaceCTTSelfReducible.logSpaceTruthTableSelfReducible
    (h : LogSpaceCTTSelfReducible encA A) : LogSpaceTruthTableSelfReducible encA A := by
  obtain ⟨r, q, base, hr, hq, hb, hlocal, hA⟩ := h
  refine ⟨r, q, fun p => if r p.1 = 0 then base p.1 else p.2.all id,
    hr, hq, by fun_prop, hlocal, fun a => ?_⟩
  classical
  rw [hA a]
  by_cases hz : r a = 0
  · simp [hz]
  · simp [hz, truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]

/-- Either Boolean base answer is permitted in the disjunctive definition. -/
theorem LogSpaceDTTSelfReducible.of_mem_L (h : A ∈ L encA) :
    LogSpaceDTTSelfReducible encA A := by
  obtain ⟨d, hd, hA⟩ := h
  exact ⟨fun _ => 0, Prod.fst, d, ComputableInLogSpace.const 0, by fun_prop, hd,
    fun _ _ hi => (Nat.not_lt_zero _ hi).elim, fun a => by simpa using hA a⟩

/-- Either Boolean base answer is permitted in the conjunctive definition. -/
theorem LogSpaceCTTSelfReducible.of_mem_L (h : A ∈ L encA) :
    LogSpaceCTTSelfReducible encA A := by
  obtain ⟨d, hd, hA⟩ := h
  exact ⟨fun _ => 0, Prod.fst, d, ComputableInLogSpace.const 0, by fun_prop, hd,
    fun _ _ hi => (Nat.not_lt_zero _ hi).elim, fun a => by simpa using hA a⟩

open Classical in
/-- Off-input answers are fixed; every occurrence of the forbidden input receives `b`.
This is the semantic unary dependency in Lemma 3.3(1), with no computability claim. -/
@[expose] noncomputable def truthTableUnaryDependency (A : Set α) (x : α)
    (r : β → ℕ) (q : β × ℕ → α) (d : β × List Bool → Bool) (s : β) (b : Bool) : Bool :=
  d (s, (List.range (r s)).map fun i =>
    if q (s, i) = x then b else by classical exact decide (q (s, i) ∈ A))

/-- Substitution of the actual input bit recovers the original answer word and decision. -/
theorem truthTableUnaryDependency_actual (x : α) (r : β → ℕ) (q : β × ℕ → α)
    (d : β × List Bool → Bool) (s : β) :
    truthTableUnaryDependency A x r q d s (by classical exact decide (x ∈ A)) =
      d (s, truthTableAnswers (q ⁻¹' A) r s) := by
  classical
  unfold truthTableUnaryDependency
  rw [truthTableAnswers_eq_map_range]
  congr 2
  apply List.map_congr_left
  intro i _
  split_ifs with heq
  · simp only [heq, Set.mem_preimage]
  · rfl

/-- Correctness of the reduction supplies the paper's semantic dependency equation. -/
theorem truthTableUnaryDependency_spec {B : Set β} (x : α) (r : β → ℕ)
    (q : β × ℕ → α) (d : β × List Bool → Bool)
    (hB : ∀ s, s ∈ B ↔ d (s, truthTableAnswers (q ⁻¹' A) r s) = true) (s : β) :
    (by classical exact decide (s ∈ B)) =
      truthTableUnaryDependency A x r q d s (by classical exact decide (x ∈ A)) := by
  classical
  rw [truthTableUnaryDependency_actual]
  exact Bool.eq_iff_iff.mpr (by simpa using hB s)

/-- A nonconstant unary Boolean function is id or negation, so is its own inverse.
This is the invariant update in Lemma 3.3(1); it does not assume an autoreduction. -/
theorem unary_bool_involutive_of_nonconstant (h : Bool → Bool) (hne : h false ≠ h true) :
    ∀ b, h (h b) = b := by
  intro b
  cases hf : h false <;> cases ht : h true <;> cases b <;> simp_all

/-- The dependency update restores the input bit from the selected child bit.
The previous path's polarity need not be accumulated: the new dependency relates the child
straight to the original input bit. -/
theorem unary_bool_dependency_update (h : Bool → Bool) (hne : h false ≠ h true)
    {a b : Bool} (hb : b = h a) : a = h b := by
  rw [hb, unary_bool_involutive_of_nonconstant h hne]

end Cslib.Complexity
