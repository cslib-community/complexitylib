/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Closure.Approximator
public import Complexity.Computability.Circuit.Monotone.Clique.Positive

/-!
# Positive errors of closed clique approximators

On the complete graph on a set `c` of `k` vertices, a closed family is accepted exactly when one of
its sets lies in `c` (`Cslib.Circuits.Monotone.Closure.Approximator.accepts_ofFinset_iff`). Closing
only adds sets, so constants and disjunctions make no positive errors. A conjunction errs on `c`
only if each argument has a set in `c` but none of their unions of at most `l` vertices is in both:
a closed family contains every set of at most `l` vertices above one of its members. So the minimal
sets `X` and `Y` of the two arguments inside `c` have more than `l` vertices together, and one of
them has at least `l / 2 + 1` vertices [Alon and Boppana, proof of Lemma 3.8, Claim 2]
[AlonBoppana1987].

A closed family has at most `(r - 1) ^ j` minimal sets of `j` vertices
(`Cslib.Circuits.Monotone.Closure.card_filter_minimals_le`), each inside `C(n - j, k - j)` of the
`k`-sets. So a conjunction errs on at most
`2 * ∑ j ∈ [l / 2 + 1, l], (r - 1) ^ j * C(n - j, k - j)` of the `k`-sets
(`Cslib.Circuits.Monotone.Closure.Positive.errorCap`). Only one set of the pair is charged, which is
what removes the square of the family bound from Razborov's estimate
(`Cslib.Circuits.Monotone.Positive.errorCap`).

## Main definitions

* `Cslib.Circuits.Monotone.Closure.Positive.errorCap`,
  `Cslib.Circuits.Monotone.Closure.Positive.errorCost`,
  `Cslib.Circuits.Monotone.Closure.Positive.exceptions`: the per-conjunction error cap, the
  per-operation error cost and the positive exceptions of a gate.
* `Cslib.Circuits.Monotone.Closure.Positive.scheme`: the approximation scheme on complete graphs.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Closure.Positive

open Cslib.Circuits.Clique Finset Cslib.Circuits.Monotone.Closure.Approximator
open Cslib.Circuits.Monotone.Positive (superCliques mem_superCliques card_superCliques)

variable {n k r l : ℕ}

/-- The `k`-sets containing a minimal set of at least `l / 2 + 1` vertices of a family. -/
def largeMinimalCliques (n k l : ℕ) (F : Finset (Finset (Fin n))) : Finset (CliqueSet n k) :=
  ((minimals F).filter (l / 2 + 1 ≤ ·.card)).biUnion (superCliques n k)

/-- The number of positive errors charged to a conjunction. -/
def errorCap (n k r l : ℕ) : ℕ :=
  2 * ∑ j ∈ Icc (l / 2 + 1) l, (r - 1) ^ j * (n - j).choose (k - j)

/-- A closed family has at most `∑ j ∈ [l / 2 + 1, l], (r - 1) ^ j * C(n - j, k - j)` of the
`k`-sets containing one of its minimal sets of at least `l / 2 + 1` vertices. -/
theorem card_largeMinimalCliques_le (hr : 2 ≤ r) (hlk : l ≤ k) {F : Finset (Finset (Fin n))}
    (hF : IsClosed r l F) (hFl : ∀ s ∈ F, s.card ≤ l) :
    (largeMinimalCliques n k l F).card ≤
      ∑ j ∈ Icc (l / 2 + 1) l, (r - 1) ^ j * (n - j).choose (k - j) := by
  set M := (minimals F).filter (l / 2 + 1 ≤ ·.card)
  have hM (W) (hW : W ∈ M) : W.card ≤ l := hFl W (mem_filter.1 (mem_filter.1 hW).1).1
  calc (largeMinimalCliques n k l F).card ≤ ∑ W ∈ M, (superCliques n k W).card := card_biUnion_le
    _ = ∑ W ∈ M, (n - W.card).choose (k - W.card) :=
        sum_congr rfl fun W hW => card_superCliques ((hM W hW).trans hlk)
    _ = ∑ j ∈ Icc (l / 2 + 1) l, ∑ W ∈ M with W.card = j, (n - W.card).choose (k - W.card) :=
        (sum_fiberwise_of_maps_to (fun W hW => mem_Icc.2 ⟨(mem_filter.1 hW).2, hM W hW⟩) _).symm
    _ = ∑ j ∈ Icc (l / 2 + 1) l, (M.filter (·.card = j)).card * (n - j).choose (k - j) :=
        sum_congr rfl fun j _ => by
          rw [sum_congr rfl fun W hW => by rw [(mem_filter.1 hW).2], sum_const, smul_eq_mul]
    _ ≤ ∑ j ∈ Icc (l / 2 + 1) l, (r - 1) ^ j * (n - j).choose (k - j) :=
        sum_le_sum fun j hj => Nat.mul_le_mul_right _ <|
          (card_le_card fun W hW => mem_filter.2 ⟨(mem_filter.1 (mem_filter.1 hW).1).1,
            (mem_filter.1 hW).2.le⟩).trans (card_filter_minimals_le hr hF (mem_Icc.1 hj).2)

/-- Only conjunctions make positive errors. -/
def errorCost (n k r l : ℕ) : signature.Op → ℕ
  | .and => errorCap n k r l
  | _ => 0

/-- The positive errors of a gate: for a conjunction, the `k`-sets containing a minimal set of at
least `l / 2 + 1` vertices of either argument. -/
def exceptions (n k : ℕ) :
    (op : Op) → (Fin (signature.Arity op) → Approximator n r l) → Finset (CliqueSet n k)
  | .and, A => largeMinimalCliques n k l (A 0).terms ∪ largeMinimalCliques n k l (A 1).terms
  | _, _ => ∅

/-- For `r ≥ 2` and `l ≤ k`, the number of positive exceptions at an `op` gate is at most
`errorCost n k r l op`. -/
theorem card_exceptions_le (hr : 2 ≤ r) (hlk : l ≤ k) (op : Op)
    (A : Fin (signature.Arity op) → Approximator n r l) :
    (exceptions n k op A).card ≤ errorCost n k r l op := by
  cases op with
  | and =>
    refine (card_union_le _ _).trans ?_
    rw [errorCost, errorCap, two_mul]
    exact Nat.add_le_add
      (card_largeMinimalCliques_le hr hlk (A 0).isClosed (A 0).card_le_of_mem)
      (card_largeMinimalCliques_le hr hlk (A 1).isClosed (A 1).card_le_of_mem)
  | const | or => simp [exceptions]

/-- Away from its exceptions, a gate is positively correct on complete graphs. -/
theorem gate_correct (op : Op) (A : Fin (signature.Arity op) → Approximator n r l)
    (c : CliqueSet n k) (hc : c ∉ exceptions n k op A) :
    Monotone.interpretation op (fun i => (A i).decode (ofFinset c.1)) ≤
      (Approximator.interpretation op A).decode (ofFinset c.1) := by
  rw [Bool.le_iff_imp]
  intro h
  rw [decode_eq_true, terms_interpretation]
  refine Accepts.of_forall_exists_subset ?_ fun s hs => ⟨s, subset_closure _ hs, subset_rfl⟩
  cases op with
  | const b =>
    rw [interpretation_const] at h
    subst h
    exact ⟨∅, by simp [Approximator.gateTerms], (contains_ofFinset c.1).mono (empty_subset _)⟩
  | or =>
    rw [interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true] at h
    rcases h with ⟨s, hs, hcs⟩ | ⟨s, hs, hcs⟩
    · exact ⟨s, mem_union_left _ hs, hcs⟩
    · exact ⟨s, mem_union_right _ hs, hcs⟩
  | and =>
    rw [interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true,
      accepts_ofFinset_iff (A 0).isClosed, accepts_ofFinset_iff (A 1).isClosed] at h
    obtain ⟨⟨X₀, hX₀, hX₀c⟩, ⟨Y₀, hY₀, hY₀c⟩⟩ := h
    obtain ⟨X, hX, hXX₀⟩ := exists_mem_minimals_subset hX₀
    obtain ⟨Y, hY, hYY₀⟩ := exists_mem_minimals_subset hY₀
    have hXc := hXX₀.trans hX₀c
    have hYc := hYY₀.trans hY₀c
    by_cases hXY : (X ∪ Y).card ≤ l
    · refine ⟨X ∪ Y, mem_inter.2 ⟨?_, ?_⟩, (contains_ofFinset c.1).mono (union_subset hXc hYc)⟩
      · exact (A 0).isClosed.mem_of_subset (mem_filter.1 hX).1 subset_union_left hXY
      · exact (A 1).isClosed.mem_of_subset (mem_filter.1 hY).1 subset_union_right hXY
    · refine absurd ?_ hc
      have := card_union_le X Y
      by_cases hXl : l / 2 + 1 ≤ X.card
      · exact mem_union_left _ (mem_biUnion.2 ⟨X, mem_filter.2 ⟨hX, hXl⟩,
          mem_superCliques.2 hXc⟩)
      · exact mem_union_right _ (mem_biUnion.2 ⟨Y, mem_filter.2 ⟨hY, by omega⟩,
          mem_superCliques.2 hYc⟩)

variable [Fact (2 ≤ r)]

/-- **Positive errors.** The approximation scheme on the complete graphs on `k`-sets: the
approximate value is at least the exact one away from the exceptions of the conjunctions. -/
def scheme (hl : 2 ≤ l) (hlk : l ≤ k) :
    Approximation.Scheme Monotone.interpretation (Approximator.interpretation (n := n) (r := r))
      (fun (A : Approximator n r l) (c : CliqueSet n k) => A.decode (ofFinset c.1))
      (fun c => ofFinset c.1) Approximator.input where
  relation := (· ≤ ·)
  relation_trans := le_trans
  map_relation op _ _ h := interpretation_mono op h
  errorCost := errorCost n k r l
  exceptions := exceptions n k
  input_correct c i := by rw [decode_input hl]
  gate_correct := gate_correct
  exceptions_card_le := card_exceptions_le Fact.out hlk

end Cslib.Circuits.Monotone.Closure.Positive
