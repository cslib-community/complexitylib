/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Line
import CslibFrontier.Foundations.Combinatorics.LineCode.Menu.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# The collision tail

Choose a direction for each of `k` requests independently and uniformly among the nonzero
vectors of `K ^ ℓ`. A fixed point other than the target blocks `Fintype.card K - 1` of the
`Fintype.card K ^ ℓ - 1` directions, so the line of one request meets a fixed set `B` for at most
`#B * (Fintype.card K - 1)` directions. If fewer than half of the requests are clean, then a
collision cut (`exists_collisionCut`) selects `⌈k / 4⌉` requests whose lines meet the occupied
points or the lines of requests outside the selection. Once the directions outside the selection
are fixed, these events concern distinct coordinates, so conditional counting
(`card_filter_forall_mem_le`) bounds them by a product. A union bound over the selections shows
that, under the budget `256 * ((#occupied + k * (q - 1)) * (q - 1)) ≤ q ^ ℓ - 1`, at most a
`2 ^ (-k)` fraction of the direction tuples leave fewer than half of the requests clean.

Targets may repeat and may be occupied: the bound counts every tuple of targets and every
occupied set.

## Main results

* `Cslib.LineCode.card_filter_two_mul_card_isClean_lt_mul_two_pow_le`: the collision tail.

## References

* Adapted, with nonzero vectors in place of projective directions, from
  MassProduction/Nonuniform/CollisionTail.lean and MassProduction/Nonuniform/PhaseMenu.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ k : ℕ}

/-- The occupied points together with the lines of the requests outside `S`, whose directions
are `y`. -/
private def outsidePoints (occupied : Finset (Fin ℓ → K)) (targets : Fin k → Fin ℓ → K)
    (S : Finset (Fin k)) (y : {j // j ∉ S} → {v : Fin ℓ → K // v ≠ 0}) : Finset (Fin ℓ → K) :=
  occupied ∪ univ.biUnion fun j => puncturedLine (targets j.1) (y j).1

private theorem card_outsidePoints_le (occupied : Finset (Fin ℓ → K))
    (targets : Fin k → Fin ℓ → K) (S : Finset (Fin k))
    (y : {j // j ∉ S} → {v : Fin ℓ → K // v ≠ 0}) :
    #(outsidePoints occupied targets S y) ≤ #occupied + k * (Fintype.card K - 1) := by
  calc #(outsidePoints occupied targets S y)
      ≤ #occupied + #(univ.biUnion fun j => puncturedLine (targets j.1) (y j).1) :=
        card_union_le _ _
    _ ≤ #occupied + ∑ j, #(puncturedLine (targets j.1) (y j).1) :=
        Nat.add_le_add_left card_biUnion_le _
    _ ≤ #occupied + ∑ _j : {j // j ∉ S}, (Fintype.card K - 1) :=
        Nat.add_le_add_left (sum_le_sum fun j _ => card_puncturedLine_le _ _) _
    _ = #occupied + Fintype.card {j // j ∉ S} * (Fintype.card K - 1) := by
        rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ #occupied + k * (Fintype.card K - 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _
          ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin k))) _

private theorem card_filter_subtype_nonzero (p : (Fin ℓ → K) → Prop) [DecidablePred p] :
    #{v : {v : Fin ℓ → K // v ≠ 0} | p v.1} = #{v ∈ univ.erase 0 | p v} := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext v
  simp [and_comm]

/-- If fewer than half of the requests are clean, then some `⌈k / 4⌉` requests have lines
meeting the occupied points or the lines of the requests outside them. -/
private theorem exists_cut (occupied : Finset (Fin ℓ → K)) (targets : Fin k → Fin ℓ → K)
    (d : Fin k → {v : Fin ℓ → K // v ≠ 0})
    (hd : 2 * #{i | IsClean occupied targets (fun j => (d j).1) i} < k) :
    ∃ S ∈ powersetCard ((k + 3) / 4) univ, ∀ i ∈ S,
      ¬Disjoint (puncturedLine (targets i) (d i).1)
        (outsidePoints occupied targets S fun j => d j) := by
  let L : Fin k → Finset (Fin ℓ → K) := fun i => puncturedLine (targets i) (d i).1
  let G : SimpleGraph (Fin k) :=
    { Adj := fun i j => i ≠ j ∧ ¬Disjoint (L i) (L j)
      symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  set bad : Finset (Fin k) := {i | ¬IsClean occupied targets (fun j => (d j).1) i}
  have hcard : #{i | IsClean occupied targets (fun j => (d j).1) i} + #bad = k := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hnon : ∀ i ∈ bad, ¬Disjoint (L i) occupied ∨ ∃ j, G.Adj i j := by
    intro i hi
    have hi : ¬(Disjoint (L i) occupied ∧ ∀ j, j ≠ i → Disjoint (L i) (L j)) := (mem_filter.mp hi).2
    by_cases ho : Disjoint (L i) occupied
    · exact Or.inr (by_contra fun hall =>
        hi ⟨ho, fun j hji => by_contra fun hij => hall ⟨j, hji.symm, hij⟩⟩)
    · exact Or.inl ho
  obtain ⟨S₀, hS₀, hbadS₀, hwit⟩ := exists_collisionCut G _ bad hnon
  obtain ⟨S, hSS₀, hS⟩ := exists_subset_card_eq (show (k + 3) / 4 ≤ #S₀ by omega)
  refine ⟨S, mem_powersetCard.mpr ⟨subset_univ _, hS⟩, fun i hi hdisj => ?_⟩
  rcases hwit i (hSS₀ hi) with ho | ⟨j, hj, hij⟩
  · exact ho (hdisj.mono_right subset_union_left)
  · have hjS : j ∉ S := fun h => hj (hSS₀ h)
    refine hij.2 (hdisj.mono_right (subset_union_right.trans' ?_))
    exact subset_biUnion_of_mem (fun j : {j // j ∉ S} => puncturedLine (targets j) (d j).1)
      (mem_univ ⟨j, hjS⟩)

/-- For a fixed set `S` of requests, at most `(q ^ ℓ - 1) ^ (k - #S) * M ^ #S` direction tuples
make every line of `S` meet the occupied points or the lines outside `S`, where
`M = (#occupied + k * (q - 1)) * (q - 1)`. -/
private theorem card_cutFailures_le (occupied : Finset (Fin ℓ → K))
    (targets : Fin k → Fin ℓ → K) (S : Finset (Fin k)) :
    #{d : Fin k → {v : Fin ℓ → K // v ≠ 0} | ∀ i ∈ S,
        ¬Disjoint (puncturedLine (targets i) (d i).1)
          (outsidePoints occupied targets S fun j => d j)} ≤
      (Fintype.card K ^ ℓ - 1) ^ (k - #S) *
        ((#occupied + k * (Fintype.card K - 1)) * (Fintype.card K - 1)) ^ #S := by
  let A : ({j // j ∉ S} → {v : Fin ℓ → K // v ≠ 0}) → Fin k →
      Finset {v : Fin ℓ → K // v ≠ 0} := fun y i =>
    {v | ¬Disjoint (puncturedLine (targets i) v.1) (outsidePoints occupied targets S y)}
  have hA : ∀ y, ∀ i ∈ S,
      #(A y i) ≤ (#occupied + k * (Fintype.card K - 1)) * (Fintype.card K - 1) := by
    intro y i _
    calc #(A y i)
        = #{v ∈ univ.erase 0 |
            ¬Disjoint (puncturedLine (targets i) v) (outsidePoints occupied targets S y)} :=
          card_filter_subtype_nonzero fun v =>
            ¬Disjoint (puncturedLine (targets i) v) (outsidePoints occupied targets S y)
      _ ≤ #((outsidePoints occupied targets S y).erase (targets i)) * (Fintype.card K - 1) :=
          card_filter_not_disjoint_puncturedLine_le _ _
      _ ≤ #(outsidePoints occupied targets S y) * (Fintype.card K - 1) :=
          Nat.mul_le_mul_right _ (card_erase_le)
      _ ≤ (#occupied + k * (Fintype.card K - 1)) * (Fintype.card K - 1) :=
          Nat.mul_le_mul_right _ (card_outsidePoints_le _ _ _ _)
  have h := card_filter_forall_mem_le S A _ hA
  rw [card_subtype_ne_zero, Fintype.card_fin] at h
  refine (card_le_card fun d hd => ?_).trans h
  exact mem_filter.mpr
    ⟨mem_univ _, fun i hi => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd).2 i hi⟩⟩

/-- **Collision tail.** Under the budget `256 * ((#occupied + k * (q - 1)) * (q - 1)) ≤ q ^ ℓ - 1`,
where `q = Fintype.card K`, at most a `2 ^ (-k)` fraction of the tuples of nonzero directions
leave fewer than half of the `k` requests clean, for every occupied set and every tuple of
targets. -/
theorem card_filter_two_mul_card_isClean_lt_mul_two_pow_le (occupied : Finset (Fin ℓ → K))
    (targets : Fin k → Fin ℓ → K)
    (hbudget : 256 * ((#occupied + k * (Fintype.card K - 1)) * (Fintype.card K - 1)) ≤
      Fintype.card K ^ ℓ - 1) :
    #{d : Fin k → {v : Fin ℓ → K // v ≠ 0} |
        2 * #{i | IsClean occupied targets (fun j => (d j).1) i} < k} * 2 ^ k ≤
      (Fintype.card K ^ ℓ - 1) ^ k := by
  set n := Fintype.card K ^ ℓ - 1
  set M := (#occupied + k * (Fintype.card K - 1)) * (Fintype.card K - 1)
  set s := (k + 3) / 4 with hs
  have hfail : #{d : Fin k → {v : Fin ℓ → K // v ≠ 0} |
      2 * #{i | IsClean occupied targets (fun j => (d j).1) i} < k} ≤
        2 ^ k * (n ^ (k - s) * M ^ s) := by
    calc _ ≤ #((powersetCard s univ).biUnion fun S =>
            ({d : Fin k → {v : Fin ℓ → K // v ≠ 0} | ∀ i ∈ S,
              ¬Disjoint (puncturedLine (targets i) (d i).1)
                (outsidePoints occupied targets S fun j => d j)} : Finset _)) := by
          refine card_le_card fun d hd => ?_
          obtain ⟨S, hS, hdS⟩ := exists_cut occupied targets d (mem_filter.mp hd).2
          exact mem_biUnion.mpr ⟨S, hS, mem_filter.mpr ⟨mem_univ _, hdS⟩⟩
      _ ≤ ∑ S ∈ powersetCard s univ, #({d : Fin k → {v : Fin ℓ → K // v ≠ 0} | ∀ i ∈ S,
            ¬Disjoint (puncturedLine (targets i) (d i).1)
              (outsidePoints occupied targets S fun j => d j)} : Finset _) := card_biUnion_le
      _ ≤ ∑ _S ∈ powersetCard s univ, n ^ (k - s) * M ^ s := by
          refine sum_le_sum fun S hS => ?_
          have h := card_cutFailures_le occupied targets S
          rwa [(mem_powersetCard.mp hS).2] at h
      _ = k.choose s * (n ^ (k - s) * M ^ s) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ 2 ^ k * (n ^ (k - s) * M ^ s) := Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
  have hsk : s ≤ k := by omega
  have hpow : 2 ^ (2 * k) ≤ 256 ^ s := by
    rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
    exact Nat.pow_le_pow_right two_pos (by omega)
  calc _ ≤ 2 ^ k * (n ^ (k - s) * M ^ s) * 2 ^ k := Nat.mul_le_mul_right _ hfail
    _ = 2 ^ (2 * k) * M ^ s * n ^ (k - s) := by rw [two_mul, pow_add]; ring
    _ ≤ 256 ^ s * M ^ s * n ^ (k - s) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
    _ = (256 * M) ^ s * n ^ (k - s) := by rw [← mul_pow]
    _ ≤ n ^ s * n ^ (k - s) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbudget s)
    _ = n ^ k := by rw [← pow_add, Nat.add_sub_cancel' hsk]

end Cslib.LineCode
