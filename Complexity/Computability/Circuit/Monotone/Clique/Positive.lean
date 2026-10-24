/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Approximator
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Positive errors of clique approximators

On the complete graph on a set of `k` vertices, the approximate interpretation is wrong only when
the exact value is `true` and the approximator says `false`. Plucking only adds acceptance, so such
an error can only come from a conjunction whose two sets join to more than `w` vertices, all inside
the `k`-set. Each such joined set lies inside at most `C(n - w - 1, k - w - 1)` of the `k`-sets, and
a conjunction of two approximators has at most `sunflowerBound p w ^ 2` pairs of sets
(`Cslib.Circuits.Monotone.Positive.scheme`).

## Main definitions

* `Cslib.Circuits.Monotone.Positive.superCliques`,
  `Cslib.Circuits.Monotone.Positive.andExceptions`,
  `Cslib.Circuits.Monotone.Positive.errorCap`,
  `Cslib.Circuits.Monotone.Positive.errorCost`,
  `Cslib.Circuits.Monotone.Positive.exceptions`: the `k`-sets containing a set, the positive
  exceptions at a gate, and their per-gate error cap.
* `Cslib.Circuits.Monotone.Positive.scheme`: the approximation scheme on complete graphs.

## Main results

* `Cslib.Circuits.Monotone.Positive.card_superCliques`: the number of `k`-sets containing a set.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Positive

open Cslib.Circuits.Clique Finset Approximator

variable {n k p w : ℕ}

/-- The `k`-sets of vertices containing `s`. -/
def superCliques (n k : ℕ) (s : Finset (Fin n)) : Finset (CliqueSet n k) :=
  univ.filter fun c => s ⊆ c.1

/-- A `k`-set `c` belongs to `superCliques n k s` if and only if `s ⊆ c.1`. -/
@[simp] theorem mem_superCliques {s : Finset (Fin n)} {c : CliqueSet n k} :
    c ∈ superCliques n k s ↔ s ⊆ c.1 := by
  simp [superCliques]

/-- The number of `k`-sets containing a set `s` of at most `k` vertices. -/
theorem card_superCliques {s : Finset (Fin n)} (hs : s.card ≤ k) :
    (superCliques n k s).card = (n - s.card).choose (k - s.card) := by
  have e : superCliques n k s = (((univ : Finset (Fin n)).powersetCard k).filter (s ⊆ ·)).attach.map
      ⟨fun c => ⟨c.1, (mem_filter.1 c.2).1⟩, fun a b h => Subtype.ext (by simpa using h)⟩ := by
    ext c
    simp only [mem_superCliques, mem_map, mem_attach, true_and]
    exact ⟨fun h => ⟨⟨c.1, mem_filter.2 ⟨c.2, h⟩⟩, rfl⟩, fun ⟨d, hd⟩ => hd ▸ (mem_filter.1 d.2).2⟩
  rw [e, card_map, card_attach]
  simpa using card_filter_powersetCard_subset s (univ : Finset (Fin n)) k (by simp) hs

/-- A set of more than `w` vertices lies inside at most `C(n - w - 1, k - w - 1)` of the
`k`-sets. -/
private theorem card_superCliques_le (hk : w + 1 ≤ k) {s : Finset (Fin n)} (hs : w < s.card) :
    (superCliques n k s).card ≤ (n - (w + 1)).choose (k - (w + 1)) := by
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (s := s) (n := w + 1) (by omega)
  calc (superCliques n k s).card ≤ (superCliques n k t).card :=
        card_le_card fun c hc => (mem_superCliques.2 (hts.trans (mem_superCliques.1 hc)))
    _ = (n - (w + 1)).choose (k - (w + 1)) := by rw [card_superCliques (by omega), ht]

/-- The positive errors of a conjunction of two families: the `k`-sets containing a joined pair of
more than `w` vertices. -/
def andExceptions (n k w : ℕ) (F G : Finset (Finset (Fin n))) : Finset (CliqueSet n k) :=
  ((F ×ˢ G).filter fun st => w < (join st.1 st.2).card).biUnion fun st =>
    superCliques n k (join st.1 st.2)

private theorem card_andExceptions_le (hk : w + 1 ≤ k) (F G : Finset (Finset (Fin n))) :
    (andExceptions n k w F G).card ≤ F.card * G.card * (n - (w + 1)).choose (k - (w + 1)) := by
  calc (andExceptions n k w F G).card
      ≤ ∑ st ∈ (F ×ˢ G).filter fun st => w < (join st.1 st.2).card,
          (superCliques n k (join st.1 st.2)).card := card_biUnion_le
    _ ≤ ∑ _st ∈ F ×ˢ G, (n - (w + 1)).choose (k - (w + 1)) :=
        (sum_le_sum fun st hst => card_superCliques_le hk (mem_filter.1 hst).2).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)
    _ = F.card * G.card * (n - (w + 1)).choose (k - (w + 1)) := by
        rw [sum_const, card_product, smul_eq_mul]

/-- The number of positive errors charged to a conjunction. -/
def errorCap (n k p w : ℕ) : ℕ :=
  sunflowerBound p w ^ 2 * (n - (w + 1)).choose (k - (w + 1))

/-- Only conjunctions make positive errors. -/
def errorCost (n k p w : ℕ) : signature.Op → ℕ
  | .and => errorCap n k p w
  | _ => 0

/-- The positive errors of a gate. -/
def exceptions (n k : ℕ) :
    (op : Op) → (Fin (signature.Arity op) → Approximator n p w) → Finset (CliqueSet n k)
  | .and, A => andExceptions n k w (A 0).terms (A 1).terms
  | _, _ => ∅

/-- When `w + 1 ≤ k`, the number of positive exceptions at an `op` gate is at most
`errorCost n k p w op`. -/
theorem card_exceptions_le (hk : w + 1 ≤ k) (op : Op)
    (A : Fin (signature.Arity op) → Approximator n p w) :
    (exceptions n k op A).card ≤ errorCost n k p w op := by
  cases op with
  | and =>
    refine (card_andExceptions_le hk _ _).trans ?_
    rw [errorCost, errorCap, pow_two]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (A 0).card_le (A 1).card_le)
  | const | or => simp [exceptions]

variable [Fact (2 ≤ p)]

/-- Away from its exceptions, a gate is positively correct on complete graphs. -/
theorem gate_correct (hw : 1 ≤ w) (op : Op) (A : Fin (signature.Arity op) → Approximator n p w)
    (c : CliqueSet n k) (hc : c ∉ exceptions n k op A) :
    Monotone.interpretation op (fun i => (A i).decode (ofFinset c.1)) ≤
      (Approximator.interpretation op A).decode (ofFinset c.1) := by
  rw [Bool.le_iff_imp]
  intro h
  rw [decode_eq_true, terms_interpretation]
  refine Accepts.of_forall_exists_subset ?_ fun _ hs => exists_subset_of_mem_pluckNormalForm hs
  cases op with
  | const b =>
    rw [interpretation_const] at h
    subst h
    exact ⟨∅, by simp [gateTerms], contains_of_card_le_one _ (by simp)⟩
  | or =>
    rw [interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true] at h
    rcases h with ⟨s, hs, hcs⟩ | ⟨s, hs, hcs⟩
    · exact ⟨s, mem_filter.2 ⟨mem_union_left _ hs, (A 0).card_le_of_mem s hs⟩, hcs⟩
    · exact ⟨s, mem_filter.2 ⟨mem_union_right _ hs, (A 1).card_le_of_mem s hs⟩, hcs⟩
  | and =>
    rw [interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true] at h
    obtain ⟨⟨s, hs, hcs⟩, ⟨t, ht, hct⟩⟩ := h
    have hjoin := contains_join_ofFinset hcs hct
    have hjw : (join s t).card ≤ w := by
      by_contra hjw
      have hsub : join s t ⊆ c.1 := subset_of_contains_ofFinset (by omega) hjoin
      exact hc (mem_biUnion.2 ⟨(s, t), mem_filter.2 ⟨mem_product.2 ⟨hs, ht⟩, not_le.1 hjw⟩,
        mem_superCliques.2 hsub⟩)
    exact ⟨join s t, mem_filter.2 ⟨mem_image.2 ⟨(s, t), mem_product.2 ⟨hs, ht⟩, rfl⟩, hjw⟩, hjoin⟩

/-- **Positive errors.** The approximation scheme on the complete graphs on `k`-sets: the
approximate value is at least the exact one away from the exceptions of the conjunctions. -/
def scheme (hw : 2 ≤ w) (hk : w + 1 ≤ k) :
    Approximation.Scheme Monotone.interpretation (Approximator.interpretation (n := n) (p := p))
      (fun (A : Approximator n p w) (c : CliqueSet n k) => A.decode (ofFinset c.1))
      (fun c => ofFinset c.1) Approximator.input where
  relation := (· ≤ ·)
  relation_trans := le_trans
  map_relation op _ _ h := interpretation_mono op h
  errorCost := errorCost n k p w
  exceptions := exceptions n k
  input_correct c i := by rw [decode_input hw]
  gate_correct := gate_correct (by omega)
  exceptions_card_le := card_exceptions_le hk

end Cslib.Circuits.Monotone.Positive
