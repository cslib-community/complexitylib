/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Approximation
public import Complexity.Computability.Circuit.Clique
public import Complexity.Computability.Circuit.Monotone.Basic
public import Complexity.Foundations.Combinatorics.Sunflower.Pluck

/-!
# Clique approximators

Razborov's method of approximations for the clique function replaces the value of every gate of a
monotone circuit by an *approximator*: a family of at most `sunflowerBound p w` sets of at most `w`
vertices, read as the disjunction of the indicators "all edges inside `s`"
(`Cslib.Circuits.Monotone.Approximator.decode`). An input variable is approximated by its edge, a
disjunction by the union of the families, and a conjunction by the pairwise unions of their sets;
sets of more than `w` vertices are dropped, and sunflowers with `p` petals are plucked
(`Cslib.pluckNormalForm`) to keep the family small. Sets of at most one vertex contain no edges
and so stand for `true`; they are dropped from a pairwise union rather than joined
(`Cslib.Circuits.Monotone.join`).

The approximate interpretation (`Cslib.Circuits.Monotone.Approximator.interpretation`) makes errors
on the two kinds of test inputs, counted in
`Complexity/Computability/Circuit/Monotone/Clique/Positive.lean` and
`Complexity/Computability/Circuit/Monotone/Clique/Negative.lean`.

## Main definitions

* `Cslib.Circuits.Monotone.Accepts`: a family of vertex sets accepts an input.
* `Cslib.Circuits.Monotone.gateTerms`: the vertex sets produced at a gate before plucking.
* `Cslib.Circuits.Monotone.Approximator`, `Cslib.Circuits.Monotone.Approximator.input`,
  `Cslib.Circuits.Monotone.Approximator.interpretation`.

## References

* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique Finset

variable {n p w : ℕ}

/-- A family of vertex sets accepts an input when the input contains all edges inside one of the
sets. -/
def Accepts (F : Finset (Finset (Fin n))) (x : Fin (edgeCount n) → Bool) : Prop :=
  ∃ s ∈ F, Contains x s

/-- Whether a family of vertex sets accepts an input is decidable. -/
noncomputable instance (F : Finset (Finset (Fin n))) (x : Fin (edgeCount n) → Bool) :
    Decidable (Accepts F x) :=
  inferInstanceAs (Decidable (∃ s ∈ F, Contains x s))

/-- A family accepts whatever a family whose every set contains one of its sets accepts. -/
theorem Accepts.of_forall_exists_subset {F G : Finset (Finset (Fin n))}
    {x : Fin (edgeCount n) → Bool} (hF : Accepts F x) (h : ∀ s ∈ F, ∃ t ∈ G, t ⊆ s) :
    Accepts G x :=
  let ⟨s, hs, hxs⟩ := hF
  let ⟨t, ht, hts⟩ := h s hs
  ⟨t, ht, hxs.mono hts⟩

/-- A set of at most one vertex contains no edge. -/
theorem contains_of_card_le_one (x : Fin (edgeCount n) → Bool) {s : Finset (Fin n)}
    (hs : s.card ≤ 1) : Contains x s := fun e he => by
  have := card_le_card he
  rw [Sym2.card_toFinset_of_not_isDiag _ e.2] at this
  omega

/-- The input `x` contains all edges inside the vertices of an edge exactly when it has the
edge. -/
theorem contains_toFinset_iff {x : Fin (edgeCount n) → Bool} {e : Edge n} :
    Contains x e.1.toFinset ↔ x (edgeEquiv n e) = true := by
  refine ⟨fun h => h e subset_rfl, fun h e' he' => ?_⟩
  have heq : e'.1.toFinset = e.1.toFinset := eq_of_subset_of_card_le he' (by
    rw [Sym2.card_toFinset_of_not_isDiag _ e.2, Sym2.card_toFinset_of_not_isDiag _ e'.2])
  have : e' = e := Subtype.ext (Sym2.ext fun v => by
    rw [← Sym2.mem_toFinset, heq, Sym2.mem_toFinset])
  rwa [this]

/-- The vertex set standing for the conjunction of two sets: a set of at most one vertex stands for
`true` and is dropped. -/
def join (s t : Finset (Fin n)) : Finset (Fin n) :=
  if s.card ≤ 1 then t else if t.card ≤ 1 then s else s ∪ t

/-- An input containing all edges inside the join of two sets contains all edges inside each. -/
theorem Contains.of_join {x : Fin (edgeCount n) → Bool} {s t : Finset (Fin n)}
    (h : Contains x (join s t)) : Contains x s ∧ Contains x t := by
  unfold join at h
  split_ifs at h with hs ht
  · exact ⟨contains_of_card_le_one x hs, h⟩
  · exact ⟨h, contains_of_card_le_one x ht⟩
  · exact ⟨h.mono subset_union_left, h.mono subset_union_right⟩

/-- On the complete graph on `c`, the join of two sets with all edges inside has all edges
inside. -/
theorem contains_join_ofFinset {c s t : Finset (Fin n)} (hs : Contains (ofFinset c) s)
    (ht : Contains (ofFinset c) t) : Contains (ofFinset c) (join s t) := by
  unfold join
  split_ifs with hs' ht'
  · exact ht
  · exact hs
  · exact (contains_ofFinset c).mono (union_subset (subset_of_contains_ofFinset (by omega) hs)
      (subset_of_contains_ofFinset (by omega) ht))

/-- The sets produced at a gate from the sets of its arguments, before plucking: `{∅}` or `∅` for
the constants, the union for a disjunction, and the pairwise joins for a conjunction, dropping the
sets of more than `w` vertices. -/
def gateTerms (w : ℕ) :
    (op : Op) → (Fin (signature.Arity op) → Finset (Finset (Fin n))) → Finset (Finset (Fin n))
  | .const b, _ => if b then {∅} else ∅
  | .or, F => (F 0 ∪ F 1).filter (·.card ≤ w)
  | .and, F => ((F 0 ×ˢ F 1).image fun st => join st.1 st.2).filter (·.card ≤ w)

/-- Every set in `gateTerms w op F` has at most `w` vertices. -/
theorem card_le_of_mem_gateTerms {op : Op} {F : Fin (signature.Arity op) → Finset (Finset (Fin n))}
    {s : Finset (Fin n)} (hs : s ∈ gateTerms w op F) : s.card ≤ w := by
  cases op with
  | const b => cases b <;> simp_all [gateTerms]
  | and | or => exact (mem_filter.1 hs).2

/-- An approximator: a family of at most `sunflowerBound p w` sets of at most `w` vertices. -/
structure Approximator (n p w : ℕ) where
  /-- The vertex sets. -/
  terms : Finset (Finset (Fin n))
  card_le_of_mem : ∀ s ∈ terms, s.card ≤ w
  card_le : terms.card ≤ sunflowerBound p w

namespace Approximator

/-- The truth value of an approximator on an input: whether one of its sets has all edges
inside. -/
noncomputable def decode (A : Approximator n p w) (x : Fin (edgeCount n) → Bool) : Bool :=
  decide (Accepts A.terms x)

/-- An approximator `A` decodes to `true` on `x` if and only if `Accepts A.terms x`. -/
@[simp] theorem decode_eq_true {A : Approximator n p w} {x : Fin (edgeCount n) → Bool} :
    A.decode x = true ↔ Accepts A.terms x :=
  decide_eq_true_iff

variable [Fact (2 ≤ p)]

/-- The approximator of an input variable: its edge, if `2 ≤ w`. -/
noncomputable def input (i : Fin (edgeCount n)) : Approximator n p w where
  terms := ({((edgeEquiv n).symm i).1.toFinset} : Finset (Finset (Fin n))).filter (·.card ≤ w)
  card_le_of_mem _ hs := (mem_filter.1 hs).2
  card_le := (card_filter_le _ _).trans ((card_singleton _).trans_le
    (sunflowerBound_pos Fact.out w))

/-- When `2 ≤ w`, the input approximator `input i` decodes to `x i`. -/
theorem decode_input (hw : 2 ≤ w) (i : Fin (edgeCount n)) (x : Fin (edgeCount n) → Bool) :
    (input i : Approximator n p w).decode x = x i := by
  have hcard : (((edgeEquiv n).symm i).1.toFinset).card ≤ w := by
    rw [Sym2.card_toFinset_of_not_isDiag _ ((edgeEquiv n).symm i).2]
    exact hw
  rw [Bool.eq_iff_iff, decode_eq_true, Accepts]
  simp only [input, filter_singleton, hcard, ite_true, mem_singleton, exists_eq_left,
    contains_toFinset_iff, Equiv.apply_symm_apply]

/-- The approximate interpretation of the monotone basis: compute the sets at the gate
(`gateTerms`) and pluck sunflowers with `p` petals. -/
noncomputable def interpretation : Interpretation signature (Approximator n p w) := fun op A =>
  { terms := pluckNormalForm p (gateTerms w op fun i => (A i).terms)
    card_le_of_mem := forall_card_le_pluckNormalForm fun _ => card_le_of_mem_gateTerms
    card_le := card_pluckNormalForm_le Fact.out fun _ => card_le_of_mem_gateTerms }

/-- The vertex sets of `interpretation op A` are the plucked sets of `gateTerms w op`. -/
theorem terms_interpretation (op : Op) (A : Fin (signature.Arity op) → Approximator n p w) :
    (interpretation op A).terms = pluckNormalForm p (gateTerms w op fun i => (A i).terms) :=
  rfl

end Approximator

end Cslib.Circuits.Monotone
