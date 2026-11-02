/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Approximation
public import Complexity.Computability.Circuit.BipartiteMatching
public import Complexity.Computability.Circuit.Monotone.Basic
public import Complexity.Foundations.Combinatorics.Sunflower.Closure

/-!
# Matching approximators

Razborov's method of approximations for bipartite perfect matching [Razborov1985a] replaces the
value of every gate of a monotone circuit by an *approximator*: a family of matchings with at most
`s` edges (`Cslib.Circuits.BipartiteMatching.Razborov.matchings`), read as "the graph contains one
of them" (`Cslib.Circuits.BipartiteMatching.Razborov.Accepts`), that is `r`-closed in the family of
all such matchings: it contains every matching of at most `s` edges implied by `r` of its members
(`Cslib.ImplicationClosure.IsClosed`) [Jukna, Section 9.11][Jukna2012].

An input variable is approximated by the matchings through its edge, `true` by all matchings of at
most `s` edges and `false` by none. A conjunction is approximated by the intersection of the
families, which is closed, and a disjunction by the closure of their union
(`Cslib.Circuits.BipartiteMatching.Razborov.Approximator.interpretation`). So only conjunctions make
errors on graphs with a perfect matching and only disjunctions on graphs without one; these errors
are counted in
`Complexity/Computability/Circuit/Monotone/BipartiteMatching/Positive.lean` and
`Complexity/Computability/Circuit/Monotone/BipartiteMatching/Negative.lean`.

## Main definitions

* `Cslib.Circuits.BipartiteMatching.Razborov.matchings`: the matchings with at most `s` edges.
* `Cslib.Circuits.BipartiteMatching.Razborov.Approximator`,
  `Cslib.Circuits.BipartiteMatching.Razborov.Approximator.input`,
  `Cslib.Circuits.BipartiteMatching.Razborov.Approximator.interpretation`: approximators, input
  approximators and the approximate interpretation of the monotone basis.

## Main results

* `Cslib.Circuits.BipartiteMatching.Razborov.Approximator.decode_input`: input approximators are
  exact.
* `Cslib.Circuits.BipartiteMatching.Razborov.Approximator.card_minimals_le`: an approximator has
  at most `(r - 1) ^ s` minimal matchings.

## References

* [A. A. Razborov, *Lower bounds on monotone complexity of the logical permanent*][Razborov1985a]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.BipartiteMatching

open Finset Cslib.ImplicationClosure
open Cslib.Circuits.Monotone (signature Op)

variable {n r s : ℕ}

namespace Razborov

/-- A family of edge sets accepts an input when the input contains one of them. -/
def Accepts (F : Finset (Finset (Fin n × Fin n))) (x : BitString (n * n)) : Prop :=
  ∃ W ∈ F, Contains x W

/-- Whether a family of edge sets accepts an input is decidable. -/
instance (F : Finset (Finset (Fin n × Fin n))) (x : BitString (n * n)) :
    Decidable (Accepts F x) :=
  inferInstanceAs (Decidable (∃ W ∈ F, Contains x W))

/-- The matchings with at most `s` edges: the ambient family of the approximators. -/
def matchings (n s : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  univ.filter fun E => IsMatching E ∧ E.card ≤ s

/-- An edge set is among the `matchings n s` when it is a matching with at most `s` edges. -/
@[simp] theorem mem_matchings {E : Finset (Fin n × Fin n)} :
    E ∈ matchings n s ↔ IsMatching E ∧ E.card ≤ s := by
  simp [matchings]

/-- The matchings with at most `s` edges are closed under subsets. -/
theorem mem_matchings_of_subset {E F : Finset (Fin n × Fin n)} (hE : E ∈ matchings n s)
    (hFE : F ⊆ E) : F ∈ matchings n s :=
  mem_matchings.2 ⟨(mem_matchings.1 hE).1.mono hFE, (card_le_card hFE).trans (mem_matchings.1 hE).2⟩

/-- The empty matching. -/
theorem empty_mem_matchings : (∅ : Finset (Fin n × Fin n)) ∈ matchings n s :=
  mem_matchings.2 ⟨fun _ h => absurd h (notMem_empty _), by simp⟩

/-! ### Approximators -/

/-- An approximator: an `r`-closed family of matchings with at most `s` edges. -/
structure Approximator (n r s : ℕ) where
  /-- The matchings. -/
  terms : Finset (Finset (Fin n × Fin n))
  subset_matchings : terms ⊆ matchings n s
  isClosed : IsClosed r (matchings n s) terms

namespace Approximator

/-- The truth value of an approximator on an input: whether the input contains one of its
matchings. -/
def decode (A : Approximator n r s) (x : BitString (n * n)) : Bool :=
  decide (Accepts A.terms x)

/-- An approximator `A` decodes to `true` on `x` if and only if `Accepts A.terms x`. -/
@[simp] theorem decode_eq_true {A : Approximator n r s} {x : BitString (n * n)} :
    A.decode x = true ↔ Accepts A.terms x :=
  decide_eq_true_iff

/-- The members of an approximator are matchings. -/
theorem isMatching_of_mem (A : Approximator n r s) {E : Finset (Fin n × Fin n)}
    (hE : E ∈ A.terms) : IsMatching E :=
  (mem_matchings.1 (A.subset_matchings hE)).1

/-- The members of an approximator have at most `s` edges. -/
theorem card_le_of_mem (A : Approximator n r s) {E : Finset (Fin n × Fin n)}
    (hE : E ∈ A.terms) : E.card ≤ s :=
  (mem_matchings.1 (A.subset_matchings hE)).2

/-- **Minimal matchings of an approximator.** For `r ≥ 2`, an approximator has at most
`(r - 1) ^ s` minimal matchings, by the Alon–Boppana family bound
(`Cslib.card_le_pow_of_isImplicationMinimal`) [AlonBoppana1987]. -/
theorem card_minimals_le (hr : 2 ≤ r) (A : Approximator n r s) :
    (minimals A.terms).card ≤ (r - 1) ^ s :=
  ImplicationClosure.card_minimals_le hr (fun _ hE _ hFE => mem_matchings_of_subset hE hFE)
    A.subset_matchings A.isClosed fun _ => A.card_le_of_mem

/-- The approximator of `true`: all matchings with at most `s` edges. -/
def top : Approximator n r s where
  terms := matchings n s
  subset_matchings := subset_rfl
  isClosed := isClosed_self

/-- The approximator of `false`: no matchings. -/
def bot (hr : 1 ≤ r) : Approximator n r s where
  terms := ∅
  subset_matchings := empty_subset _
  isClosed := isClosed_empty hr

/-- The approximator of a conjunction: the intersection of the families. -/
def inf (A B : Approximator n r s) : Approximator n r s where
  terms := A.terms ∩ B.terms
  subset_matchings := inter_subset_left.trans A.subset_matchings
  isClosed := A.isClosed.inter B.isClosed

/-- The approximator of a disjunction: the closure of the union of the families. -/
noncomputable def sup (A B : Approximator n r s) : Approximator n r s where
  terms := closure r (matchings n s) (A.terms ∪ B.terms)
  subset_matchings := closure_subset (union_subset A.subset_matchings B.subset_matchings)
  isClosed := isClosed_closure _

/-- `top` decodes to `true`. -/
@[simp] theorem decode_top (x : BitString (n * n)) : (top : Approximator n r s).decode x = true :=
  decode_eq_true.2 ⟨∅, empty_mem_matchings, fun _ h => absurd h (notMem_empty _)⟩

/-- `bot` decodes to `false`. -/
@[simp] theorem decode_bot (hr : 1 ≤ r) (x : BitString (n * n)) :
    (bot hr : Approximator n r s).decode x = false := by
  rw [Bool.eq_false_iff, Ne, decode_eq_true]
  exact fun ⟨_, h, _⟩ => absurd h (notMem_empty _)

variable [Fact (2 ≤ r)]

/-- The approximate interpretation of the monotone basis: `top` and `bot` for the constants, the
intersection for a conjunction and the closure of the union for a disjunction. -/
noncomputable def interpretation : Interpretation signature (Approximator n r s)
  | .const b, _ => if b then top else bot (by have : 2 ≤ r := Fact.out; omega)
  | .and, A => inf (A 0) (A 1)
  | .or, A => sup (A 0) (A 1)

/-- A constant is approximated by `top` or `bot`, and decodes to itself. -/
@[simp] theorem decode_interpretation_const (b : Bool) (A : Fin 0 → Approximator n r s)
    (x : BitString (n * n)) : (interpretation (.const b) A).decode x = b := by
  cases b <;> simp [interpretation]

/-- A conjunction is approximated by the intersection of the families. -/
@[simp] theorem terms_interpretation_and (A : Fin 2 → Approximator n r s) :
    (interpretation .and A).terms = (A 0).terms ∩ (A 1).terms :=
  rfl

/-- A disjunction is approximated by the closure of the union of the families. -/
@[simp] theorem terms_interpretation_or (A : Fin 2 → Approximator n r s) :
    (interpretation .or A).terms = closure r (matchings n s) ((A 0).terms ∪ (A 1).terms) :=
  rfl

/-- The approximator of an input variable: the matchings with at most `s` edges through its
edge. -/
def input (i : Fin (n * n)) : Approximator n r s where
  terms := (matchings n s).filter (finProdFinEquiv.symm i ∈ ·)
  subset_matchings := filter_subset _ _
  isClosed W := by
    rintro ⟨hW, V, hV, hVW⟩
    have hr : 2 ≤ r := Fact.out
    refine mem_filter.2 ⟨hW, hVW ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp) (mem_inter.2 ⟨?_, ?_⟩)⟩
    exacts [(mem_filter.1 (hV _)).2, (mem_filter.1 (hV _)).2]

/-- When `1 ≤ s`, the input approximator `input i` decodes to `x i`. -/
theorem decode_input (hs : 1 ≤ s) (i : Fin (n * n)) (x : BitString (n * n)) :
    (input i : Approximator n r s).decode x = x i := by
  rw [Bool.eq_iff_iff, decode_eq_true]
  constructor
  · rintro ⟨W, hW, hxW⟩
    have := hxW _ (mem_filter.1 hW).2
    simpa only [graph, Equiv.apply_symm_apply] using this
  · intro hx
    refine ⟨{finProdFinEquiv.symm i}, mem_filter.2 ⟨mem_matchings.2
      ⟨isMatching_singleton _, by simpa using hs⟩, mem_singleton_self _⟩, ?_⟩
    intro e he
    rw [mem_singleton.1 he]
    simpa only [graph, Equiv.apply_symm_apply] using hx

end Approximator

end Razborov

end Cslib.Circuits.BipartiteMatching
