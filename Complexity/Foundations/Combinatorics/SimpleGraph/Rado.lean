/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Nat.Bitwise
import Complexity.Foundations.Data.Nat.Bitwise.Sparse
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Rado graph

`SimpleGraph.radoGraph` is the countable random graph, realized on `ℕ` by Ackermann's bit
relation: distinct `i` and `j` are adjacent when bit `i` of `j` is set or bit `j` of `i` is set
[Ackermann1937] [Rado1964] [Libkin2004, Section 12.3].

It has the **extension property**: for disjoint finite sets `A` and `B` of vertices there is a
vertex outside `A ∪ B` adjacent to every vertex of `A` and to no vertex of `B`. A witness is
`2 ^ M + ∑ a ∈ A, 2 ^ a` for `M` larger than every element of `A ∪ B`; its set bits are read off
with `Nat.testBit_sum_two_pow`. The model-theoretic consequences (uniqueness, universality, and
the identification of the almost-sure theory of `G(n, 1/2)` with the theory of the Rado graph)
are in `Complexity.Logics.FirstOrder.ZeroOneLaw.Rado`.

## Main definitions

* `SimpleGraph.radoGraph`: the Rado graph on `ℕ`.

## Main results

* `SimpleGraph.radoGraph_adj`: adjacency in terms of `Nat.testBit`.
* `SimpleGraph.radoGraph_exists_adj`: the extension property.

## References

* [W. Ackermann, *Die Widerspruchsfreiheit der allgemeinen Mengenlehre*][Ackermann1937]
* [R. Rado, *Universal graphs and universal functions*][Rado1964]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 12.3.
-/

public section

namespace SimpleGraph

/-- The **Rado graph** on `ℕ`: distinct `i` and `j` are adjacent when bit `i` of `j` is set or bit
`j` of `i` is set (Ackermann's encoding of hereditarily finite sets) [Ackermann1937] [Rado1964]. -/
def radoGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => j.testBit i = true

/-- Two natural numbers are adjacent in the Rado graph when one of them has the other as a set
bit. Distinctness is automatic, since bit `i` of `i` is never set. -/
theorem radoGraph_adj {i j : ℕ} :
    radoGraph.Adj i j ↔ j.testBit i = true ∨ i.testBit j = true := by
  rw [radoGraph, fromRel_adj, and_iff_right_iff_imp]
  rintro h rfl
  rw [Nat.testBit_eq_false_of_lt i.lt_two_pow_self, Bool.false_eq_true, or_self] at h
  exact h

instance : DecidableRel radoGraph.Adj := fun _ _ => decidable_of_iff' _ radoGraph_adj

/-- **Extension property of the Rado graph.** For disjoint finite sets `A` and `B` of vertices,
some vertex outside `A ∪ B` is adjacent to every vertex of `A` and to no vertex of `B`. -/
theorem radoGraph_exists_adj {A B : Finset ℕ} (hAB : Disjoint A B) :
    ∃ z, z ∉ A ∧ z ∉ B ∧ (∀ a ∈ A, radoGraph.Adj z a) ∧ ∀ b ∈ B, ¬radoGraph.Adj z b := by
  classical
  let M := ∑ a ∈ A ∪ B, a + 1
  have hM : ∀ a ∈ A ∪ B, a < M := fun a ha =>
    Nat.lt_succ_of_le (Finset.single_le_sum (f := fun a => a) (fun _ _ => Nat.zero_le _) ha)
  -- The witness has bit `M` set, which places it above `A ∪ B`, and below `M` exactly the bits
  -- of `A`.
  let z := ∑ j ∈ insert M A, 2 ^ j
  have hMz : M < z :=
    M.lt_two_pow_self.trans_le (Finset.single_le_sum (f := fun j => 2 ^ j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self M A))
  have hz : ∀ a ∈ A ∪ B, radoGraph.Adj z a ↔ a ∈ A := by
    intro a ha
    have haz : a < z := (hM a ha).trans hMz
    rw [radoGraph_adj, Nat.testBit_eq_false_of_lt (haz.trans z.lt_two_pow_self),
      Bool.false_eq_true, false_or, Nat.testBit_sum_two_pow, Finset.mem_insert,
      or_iff_right (hM a ha).ne]
  refine ⟨z, fun h => ?_, fun h => ?_, fun a ha => (hz a (Finset.mem_union_left _ ha)).2 ha,
    fun b hb h => Finset.disjoint_left.1 hAB ((hz b (Finset.mem_union_right _ hb)).1 h) hb⟩
  · exact absurd hMz (hM z (Finset.mem_union_left _ h)).not_gt
  · exact absurd hMz (hM z (Finset.mem_union_right _ h)).not_gt

end SimpleGraph
