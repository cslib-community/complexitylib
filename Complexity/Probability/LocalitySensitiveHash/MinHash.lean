/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.LocalitySensitiveHash
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.WithBot
import Complexity.Probability.PMF.Uniform

/-!
# MinHash and the Jaccard similarity

A permutation `σ` of a finite linear order `α` ranks the elements of `α`. The MinHash of a finite
set `A` is the least rank `min σ(A)`, with `⊤` for the empty set (`Cslib.Probability.minHash`).
Broder's theorem ([Broder1997]; [LeskovecRajaramanUllman2020], Section 3.3.3) states that, for a
uniformly random permutation, two sets have equal MinHash values with probability exactly their
Jaccard similarity `|A ∩ B| / |A ∪ B|` (`Cslib.Probability.collisionProb_minHash`). The Jaccard
similarity of two empty sets is taken to be `1` (`Cslib.Probability.jaccard`), which makes the
identity unconditional.

Under a random permutation each element of `A ∪ B` is equally likely to have the least rank:
transposing two elements is a bijection between the permutations ranking either one first. The
MinHash values agree exactly when the element of least rank lies in `A ∩ B`.

Consequently MinHash is a `(d₁, d₂, 1 - d₁, 1 - d₂)`-sensitive family for the Jaccard distance
`1 - J` ([LeskovecRajaramanUllman2020], Section 3.6.2; `isLocalitySensitive_minHash`). Banding
`b` bands of `r` MinHash rows gives the S-curve `1 - (1 - J ^ r) ^ b`
([LeskovecRajaramanUllman2020], Section 3.4.2; `orCollisionProb_andHash_minHash`). Charikar's
triangle inequality gives the triangle inequality for the Jaccard distance
(`jaccard_triangle`).

The random permutation is a uniformly random element of the full symmetric group `Equiv.Perm α`.
Smaller min-wise independent families and the hash-based approximations used in practice are not
treated here.

## Main definitions

* `Cslib.Probability.minHash`: the least rank of a finite set under a permutation.
* `Cslib.Probability.jaccard`: the Jaccard similarity `|A ∩ B| / |A ∪ B|`, with `J(∅, ∅) = 1`.

## Main results

* `Cslib.Probability.collisionProb_minHash`: Broder's theorem `Pr[minHash σ A = minHash σ B] =
  J(A, B)`.
* `Cslib.Probability.isLocalitySensitive_minHash`: sensitivity for the Jaccard distance.
* `Cslib.Probability.orCollisionProb_andHash_minHash`: the banding S-curve for MinHash.
* `Cslib.Probability.jaccard_triangle`: the triangle inequality for the Jaccard distance, on any
  type with decidable equality.

## References

* [A. Z. Broder, *On the resemblance and containment of documents*][Broder1997]
* [J. Leskovec, A. Rajaraman, J. D. Ullman,
  *Mining of Massive Datasets*][LeskovecRajaramanUllman2020], Chapter 3.
* [M. S. Charikar, *Similarity estimation techniques from rounding algorithms*][Charikar2002]
-/

@[expose] public section

namespace Cslib.Probability

section Jaccard

variable {α : Type*} [DecidableEq α]

/-- The Jaccard similarity `|A ∩ B| / |A ∪ B|` of two finite sets, with `J(∅, ∅) = 1`. -/
def jaccard (A B : Finset α) : ℚ :=
  if A ∪ B = ∅ then 1 else ((A ∩ B).card : ℚ) / (A ∪ B).card

/-- For sets with a nonempty union, the Jaccard similarity is `|A ∩ B| / |A ∪ B|`. -/
theorem jaccard_eq_div {A B : Finset α} (h : (A ∪ B).Nonempty) :
    jaccard A B = ((A ∩ B).card : ℚ) / (A ∪ B).card :=
  ite_eq_right h.ne_empty

theorem jaccard_comm (A B : Finset α) : jaccard A B = jaccard B A := by
  rw [jaccard, jaccard, Finset.union_comm, Finset.inter_comm]

@[simp]
theorem jaccard_self (A : Finset α) : jaccard A A = 1 := by
  rw [jaccard, Finset.union_self, Finset.inter_self]
  split_ifs with hA
  · rfl
  · exact div_self (by exact_mod_cast Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hA))

theorem jaccard_nonneg (A B : Finset α) : 0 ≤ jaccard A B := by
  rw [jaccard]
  split_ifs
  · exact zero_le_one
  · positivity

theorem jaccard_le_one (A B : Finset α) : jaccard A B ≤ 1 := by
  rw [jaccard]
  split_ifs
  · exact le_rfl
  · exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card Finset.inter_subset_union)
      (Nat.cast_nonneg _)

/-- The Jaccard similarity is invariant under embeddings. -/
theorem jaccard_map {β : Type*} [DecidableEq β] (f : α ↪ β) (A B : Finset α) :
    jaccard (A.map f) (B.map f) = jaccard A B := by
  simp only [jaccard, ← Finset.map_union, ← Finset.map_inter, Finset.card_map,
    Finset.map_eq_empty]

end Jaccard

section MinHash

variable {α : Type*} [LinearOrder α]

/-- The MinHash of a finite set `A` under the ranking `σ`: the least rank `min σ(A)`, or `⊤` when
`A` is empty. -/
def minHash (σ : Equiv.Perm α) (A : Finset α) : WithTop α :=
  A.inf fun a => (σ a : WithTop α)

@[simp]
theorem minHash_empty (σ : Equiv.Perm α) : minHash σ ∅ = ⊤ :=
  Finset.inf_empty

/-- An element of least rank in `A` attains the MinHash of `A`. -/
theorem minHash_eq_of_isMin {σ : Equiv.Perm α} {A : Finset α} {s : α} (hs : s ∈ A)
    (hmin : ∀ a ∈ A, σ s ≤ σ a) : minHash σ A = σ s :=
  le_antisymm (Finset.inf_le hs) (Finset.le_inf fun a ha => WithTop.coe_le_coe.2 (hmin a ha))

variable [Fintype α]

/-- The permutations under which `s` has the least rank in `S`. -/
private def argminSet (S : Finset α) (s : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => ∀ a ∈ S, σ s ≤ σ a

private theorem exists_mem_argminSet (S : Finset α) (hS : S.Nonempty) (σ : Equiv.Perm α) :
    ∃ s ∈ S, σ ∈ argminSet S s := by
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image σ hS
  exact ⟨s, hs, Finset.mem_filter.2 ⟨Finset.mem_univ _, hmin⟩⟩

private theorem argminSet_disjoint {S : Finset α} {s t : α} (hs : s ∈ S) (ht : t ∈ S)
    (hst : s ≠ t) : Disjoint (argminSet S s) (argminSet S t) := by
  rw [Finset.disjoint_left]
  intro σ h₁ h₂
  simp only [argminSet, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  exact hst (σ.injective (le_antisymm (h₁ t ht) (h₂ s hs)))

/-- Composing with the transposition of `s` and `t` exchanges the permutations ranking `s` first
with those ranking `t` first. -/
private theorem card_argminSet_eq {S : Finset α} {s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    (argminSet S s).card = (argminSet S t).card := by
  classical
  refine Finset.card_bij' (fun σ _ => σ * Equiv.swap s t) (fun σ _ => σ * Equiv.swap s t)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [argminSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.coe_mul,
      Function.comp_apply, Equiv.swap_apply_right] at hσ ⊢
    intro a ha
    rcases eq_or_ne a s with rfl | has
    · rw [Equiv.swap_apply_left]
      exact hσ t ht
    rcases eq_or_ne a t with rfl | hat
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne has hat]
      exact hσ a ha
  · intro σ hσ
    simp only [argminSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.coe_mul,
      Function.comp_apply, Equiv.swap_apply_left] at hσ ⊢
    intro a ha
    rcases eq_or_ne a t with rfl | hat
    · rw [Equiv.swap_apply_right]
      exact hσ s hs
    rcases eq_or_ne a s with rfl | has
    · rw [Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne has hat]
      exact hσ a ha
  · intro σ _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  · intro σ _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- Each element of `S` has the least rank under the same number `|α|! / |S|` of permutations. -/
private theorem card_mul_card_argminSet {S : Finset α} {s : α} (hs : s ∈ S) :
    S.card * (argminSet S s).card = Fintype.card (Equiv.Perm α) := by
  have hcover : (Finset.univ : Finset (Equiv.Perm α)) = S.biUnion (argminSet S) := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact exists_mem_argminSet S ⟨s, hs⟩ σ
  rw [← Finset.card_univ, hcover, Finset.card_biUnion
    (fun t ht u hu htu => argminSet_disjoint ht hu htu),
    Finset.sum_congr rfl (fun t ht => card_argminSet_eq ht hs), Finset.sum_const, smul_eq_mul]

/-- If `s` has the least rank in `A ∪ B`, the MinHash values of `A` and `B` agree exactly when
`s ∈ A ∩ B`. -/
private theorem minHash_eq_minHash_iff {σ : Equiv.Perm α} {A B : Finset α} {s : α}
    (hs : s ∈ A ∪ B) (hσ : σ ∈ argminSet (A ∪ B) s) :
    minHash σ A = minHash σ B ↔ s ∈ A ∩ B := by
  simp only [argminSet, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  have hA : s ∈ A → minHash σ A = σ s := fun h =>
    minHash_eq_of_isMin h fun a ha => hσ a (Finset.mem_union_left _ ha)
  have hB : s ∈ B → minHash σ B = σ s := fun h =>
    minHash_eq_of_isMin h fun a ha => hσ a (Finset.mem_union_right _ ha)
  constructor
  · intro heq
    rw [Finset.mem_inter]
    rcases Finset.mem_union.1 hs with hsA | hsB
    · refine ⟨hsA, ?_⟩
      rw [hA hsA] at heq
      have hB0 : B.Nonempty := by
        by_contra hB0
        rw [Finset.not_nonempty_iff_eq_empty] at hB0
        rw [hB0, minHash_empty] at heq
        exact WithTop.coe_ne_top heq
      obtain ⟨t, ht, hbt⟩ := Finset.exists_mem_eq_inf B hB0 fun b => (σ b : WithTop α)
      rw [minHash, hbt] at heq
      rw [σ.injective (WithTop.coe_injective heq)]
      exact ht
    · refine ⟨?_, hsB⟩
      rw [hB hsB] at heq
      have hA0 : A.Nonempty := by
        by_contra hA0
        rw [Finset.not_nonempty_iff_eq_empty] at hA0
        rw [hA0, minHash_empty] at heq
        exact WithTop.top_ne_coe heq
      obtain ⟨t, ht, hat⟩ := Finset.exists_mem_eq_inf A hA0 fun a => (σ a : WithTop α)
      rw [minHash, hat] at heq
      rw [← σ.injective (WithTop.coe_injective heq)]
      exact ht
  · intro h
    rw [Finset.mem_inter] at h
    rw [hA h.1, hB h.2]

/-- **Broder's theorem** ([Broder1997]; [LeskovecRajaramanUllman2020], Section 3.3.3): under a
uniformly random permutation of `α`, two finite sets have equal MinHash values with probability
exactly their Jaccard similarity. -/
theorem collisionProb_minHash (A B : Finset α) :
    collisionProb (PMF.uniformOfFintype (Equiv.Perm α)) minHash A B = jaccard A B := by
  classical
  rw [collisionProb, PMF.toOuterMeasure_uniformOfFintype_toReal, jaccard]
  split_ifs with hS
  · have hA : A = ∅ := Finset.subset_empty.1 (hS ▸ Finset.subset_union_left)
    have hB : B = ∅ := Finset.subset_empty.1 (hS ▸ Finset.subset_union_right)
    subst hA hB
    simp only [Set.mem_ofPred_eq, Finset.filter_true, Finset.card_univ, Rat.cast_one]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hS
    have hcoll : Finset.univ.filter (· ∈ {σ : Equiv.Perm α | minHash σ A = minHash σ B}) =
        (A ∩ B).biUnion (argminSet (A ∪ B)) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_biUnion]
      obtain ⟨t, ht, hσ⟩ := exists_mem_argminSet (A ∪ B) ⟨s, hs⟩ σ
      rw [minHash_eq_minHash_iff ht hσ]
      constructor
      · intro h
        exact ⟨t, h, hσ⟩
      · rintro ⟨u, hu, hσu⟩
        by_contra htu
        have hne : u ≠ t := fun h => htu (h ▸ hu)
        exact Finset.disjoint_left.1 (argminSet_disjoint
          (Finset.inter_subset_union hu) ht hne) hσu hσ
    have hcard : (Finset.univ.filter
        (· ∈ {σ : Equiv.Perm α | minHash σ A = minHash σ B})).card =
        (A ∩ B).card * (argminSet (A ∪ B) s).card := by
      rw [hcoll, Finset.card_biUnion (fun t ht u hu htu => argminSet_disjoint
        (Finset.inter_subset_union ht) (Finset.inter_subset_union hu) htu),
        Finset.sum_congr rfl (fun t ht => card_argminSet_eq (Finset.inter_subset_union ht) hs),
        Finset.sum_const, smul_eq_mul]
    have htot := card_mul_card_argminSet hs
    have hpos : ((argminSet (A ∪ B) s).card : ℝ) ≠ 0 := by
      intro h0
      rw [Nat.cast_eq_zero] at h0
      rw [h0, mul_zero] at htot
      exact Fintype.card_ne_zero htot.symm
    rw [hcard, ← htot]
    push_cast
    rw [mul_div_mul_right _ _ hpos]

/-- MinHash is `(d₁, d₂, 1 - d₁, 1 - d₂)`-sensitive for the Jaccard distance `1 - J`
([LeskovecRajaramanUllman2020], Section 3.6.2). -/
theorem isLocalitySensitive_minHash (d₁ d₂ : ℝ) :
    IsLocalitySensitive (collisionProb (PMF.uniformOfFintype (Equiv.Perm α)) minHash)
      (fun A B => 1 - (jaccard A B : ℝ) ≤ d₁) (fun A B => d₂ ≤ 1 - (jaccard A B : ℝ))
      (1 - d₁) (1 - d₂) where
  le_of_near A B h := by
    rw [collisionProb_minHash]
    linarith
  le_of_far A B h := by
    rw [collisionProb_minHash]
    linarith

/-- **Banding MinHash signatures** ([LeskovecRajaramanUllman2020], Section 3.4.2): `b` bands of
`r` independent MinHash rows agree in some band with probability `1 - (1 - J ^ r) ^ b`. -/
theorem orCollisionProb_andHash_minHash (r b : ℕ) (A B : Finset α) :
    orCollisionProb (PMF.iid (PMF.uniformOfFintype (Equiv.Perm α)) r) (andHash minHash r) b A B =
      sCurve r b (jaccard A B) := by
  rw [orCollisionProb_andHash, collisionProb_minHash]

end MinHash

/-- The Jaccard distance on a finite linearly ordered universe satisfies the triangle inequality:
Charikar's argument applied to MinHash. -/
private theorem jaccard_triangle_of_linearOrder {α : Type*} [LinearOrder α] [Finite α]
    (A B C : Finset α) : 1 - jaccard A C ≤ (1 - jaccard A B) + (1 - jaccard B C) := by
  have := Fintype.ofFinite α
  have h := collisionProb_triangle (PMF.uniformOfFintype (Equiv.Perm α)) minHash A B C
  rw [collisionProb_minHash, collisionProb_minHash, collisionProb_minHash] at h
  exact_mod_cast h

/-- The Jaccard distance `1 - J` satisfies the triangle inequality, by Charikar's argument
([Charikar2002], Lemma 1) applied to MinHash. The three sets are moved into the finite universe
`A ∪ B ∪ C`, ordered arbitrarily, where Broder's theorem applies. -/
theorem jaccard_triangle {α : Type*} [DecidableEq α] (A B C : Finset α) :
    1 - jaccard A C ≤ (1 - jaccard A B) + (1 - jaccard B C) := by
  set S := A ∪ B ∪ C
  let _ : LinearOrder S := LinearOrder.lift' (Fintype.equivFin S) (Equiv.injective _)
  have hA : (A.subtype (· ∈ S)).map (Function.Embedding.subtype _) = A :=
    Finset.subtype_map_of_mem fun x hx => by simp [S, hx]
  have hB : (B.subtype (· ∈ S)).map (Function.Embedding.subtype _) = B :=
    Finset.subtype_map_of_mem fun x hx => by simp [S, hx]
  have hC : (C.subtype (· ∈ S)).map (Function.Embedding.subtype _) = C :=
    Finset.subtype_map_of_mem fun x hx => by simp [S, hx]
  have h := jaccard_triangle_of_linearOrder (A.subtype (· ∈ S)) (B.subtype (· ∈ S))
    (C.subtype (· ∈ S))
  rw [← hA, ← hB, ← hC]
  convert h using 3 <;> convert jaccard_map (Function.Embedding.subtype (· ∈ S)) _ _

end Cslib.Probability
