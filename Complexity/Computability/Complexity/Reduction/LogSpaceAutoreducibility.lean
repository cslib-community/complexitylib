/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.LogSpaceTruthTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Logspace truth-table autoreducibility

Query-avoiding versions of the indexed logspace truth-table reductions: the count, generator,
evaluator, encodings and answer word are exactly those of `LogSpaceTruthTableReducible`.
Only active queries must avoid the input; unused indices are unrestricted. Since `encA` is
injective, avoidance of instances is equivalent to avoidance of their encoded words.

## Main definitions

* `Cslib.Complexity.LogSpaceTruthTableAutoreducible`: query-avoiding truth-table reduction.
* `Cslib.Complexity.LogSpaceKTruthTableAutoreducible`: at most `k` queries on every input.
* `Cslib.Complexity.LogSpaceBTTAutoreducible`: a constant bound independent of the input.

## Main results

* `Cslib.Complexity.logSpaceKTruthTableAutoreducible_one_of_complement_witness`:
  query a complement-reduction witness and negate its answer.
* `Cslib.Complexity.LogSpaceComplete.logSpaceKTruthTableAutoreducible_one`:
  the many-one clause of Proposition 2.7 of [GlasserNguyenReitwiessnerSelmanWitek2013].

## Source mapping

The source is the expanded ECCC TR13-047 version dated 18 March 2013, Proposition 2.7(1),
printed page 5 (PDF index 4), with autoreducibility as in Definition 2.2, page 4.
For every encoded instance type, `C` is closed under set complement; completeness includes
membership and hardness for every encoded problem in `C`. On bit words with `encBits`, this
specializes to the paper's language setting. More generally the theorem retains the existing
library's explicit injective encodings. Count output uses `encUnary`, query inputs use
`encPair encA encUnary`, and evaluation uses `encPair encA encBits` with output `encBool`.
The inherited resource predicate is plain `ComputableInLogSpace`; the evaluator convention is
`L`, as documented in `LogSpaceTruthTable`. Here the evaluator just negates one bit, so no
unbounded truth-table evaluation claim is needed. The bound is **at most** one query, with a
witness asking exactly one on every input.

The proof is the paper's existing complement-reduction argument specialized to many-one
reductions, not a new proof idea. A witness for $A^c \le_m^L A$ satisfies
$x \notin A \leftrightarrow f(x) \in A$, which forces $f(x) \ne x$; negate the oracle answer.
Proposition 2.7(2,3), concerning bounded disjunctive/conjunctive completeness, is not proved
here. Neither the full paper nor an application to parity logspace is claimed.

## References

* [C. Glaßer, D. T. Nguyen, C. Reitwießner, A. L. Selman and M. Witek,
  *Autoreducibility of Complete Sets for Log-Space and Polynomial-Time Reductions*]
  [GlasserNguyenReitwiessnerSelmanWitek2013]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α}

/-- A logspace truth-table reduction to the same set, with no active query equal to its input. -/
@[expose] def LogSpaceTruthTableAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encA ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    (∀ a i, i < r a → q (a, i) ≠ a) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' A) r a) = true

/-- A query-avoiding logspace truth-table reduction with at most `k` queries on each input. -/
@[expose] def LogSpaceKTruthTableAutoreducible (k : ℕ) (encA : α ↪ List Bool)
    (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encA ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    (∀ a, r a ≤ k) ∧ (∀ a i, i < r a → q (a, i) ≠ a) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' A) r a) = true

/-- A query-avoiding logspace truth-table reduction with some constant query bound. -/
@[expose] def LogSpaceBTTAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ k, LogSpaceKTruthTableAutoreducible k encA A

/-- Forgetting query avoidance gives an ordinary logspace truth-table reduction. -/
theorem LogSpaceTruthTableAutoreducible.logSpaceTruthTableReducible
    (h : LogSpaceTruthTableAutoreducible encA A) :
    LogSpaceTruthTableReducible encA encA A A :=
  let ⟨r, q, d, hr, hq, hd, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hA⟩

/-- Forgetting query avoidance preserves the query bound. -/
theorem LogSpaceKTruthTableAutoreducible.logSpaceKTruthTableReducible {k : ℕ}
    (h : LogSpaceKTruthTableAutoreducible k encA A) :
    LogSpaceKTruthTableReducible k encA encA A A :=
  let ⟨r, q, d, hr, hq, hd, hk, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hk, hA⟩

/-- Increasing the allowed number of queries preserves autoreducibility. -/
theorem LogSpaceKTruthTableAutoreducible.mono {k k' : ℕ}
    (h : LogSpaceKTruthTableAutoreducible k encA A) (hk : k ≤ k') :
    LogSpaceKTruthTableAutoreducible k' encA A :=
  let ⟨r, q, d, hr, hq, hd, hrk, hne, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, fun a => (hrk a).trans hk, hne, hA⟩

/-- A fixed query bound witnesses bounded truth-table autoreducibility. -/
theorem LogSpaceKTruthTableAutoreducible.logSpaceBTTAutoreducible {k : ℕ}
    (h : LogSpaceKTruthTableAutoreducible k encA A) : LogSpaceBTTAutoreducible encA A :=
  ⟨k, h⟩

/-- Forgetting the constant bound gives truth-table autoreducibility, retaining avoidance. -/
theorem LogSpaceBTTAutoreducible.logSpaceTruthTableAutoreducible
    (h : LogSpaceBTTAutoreducible encA A) : LogSpaceTruthTableAutoreducible encA A :=
  let ⟨_, r, q, d, hr, hq, hd, _, hne, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hne, hA⟩

/-- A bounded autoreduction is an ordinary bounded reduction. -/
theorem LogSpaceBTTAutoreducible.logSpaceBTTReducible
    (h : LogSpaceBTTAutoreducible encA A) : LogSpaceBTTReducible encA encA A A :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.logSpaceKTruthTableReducible⟩

/-- The many-one case of the complement-reduction argument in
[GlasserNguyenReitwiessnerSelmanWitek2013], Proposition 2.7, page 5: a logspace witness reducing
`Aᶜ` to `A` cannot fix any input; query it and negate the answer. -/
theorem logSpaceKTruthTableAutoreducible_one_of_complement_witness {f : α → α}
    (hf : ComputableInLogSpace f encA encA) (hA : ∀ a, a ∉ A ↔ f a ∈ A) :
    LogSpaceKTruthTableAutoreducible 1 encA A := by
  have hne : ∀ a, f a ≠ a := by
    intro a heq
    have h := hA a
    rw [heq] at h
    tauto
  refine ⟨fun _ => 1, fun p => f p.1, fun p => !p.2.headD false,
    ComputableInLogSpace.const 1, by fun_prop, by fun_prop,
    fun _ => le_rfl, fun a _ _ => hne a, fun a => ?_⟩
  classical
  simp only [truthTableAnswers]
  simp [← hA a]

/-- A reduction from the complement suffices; query avoidance follows from its correctness. -/
theorem LogSpaceReducible.logSpaceKTruthTableAutoreducible_one_of_compl
    (h : LogSpaceReducible encA encA Aᶜ A) : LogSpaceKTruthTableAutoreducible 1 encA A := by
  obtain ⟨f, hf, hA⟩ := h
  exact logSpaceKTruthTableAutoreducible_one_of_complement_witness hf hA

/-- Proposition 2.7(1) of the expanded ECCC version of
[GlasserNguyenReitwiessnerSelmanWitek2013], page 5: many-one complete sets of a complement-closed
class are one-query truth-table autoreducible in logspace. -/
theorem LogSpaceComplete.logSpaceKTruthTableAutoreducible_one
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (h : LogSpaceComplete C encA A)
    (hcompl : ∀ {β : Type} (enc : β ↪ List Bool) (B : Set β), B ∈ C enc → Bᶜ ∈ C enc) :
    LogSpaceKTruthTableAutoreducible 1 encA A :=
  (h.2 encA Aᶜ (hcompl encA A h.1)).logSpaceKTruthTableAutoreducible_one_of_compl

end Cslib.Complexity
