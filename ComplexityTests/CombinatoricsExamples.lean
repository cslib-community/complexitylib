/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.CentralBinomial
import Complexity.Foundations.Combinatorics.DepthReduction
import Complexity.Foundations.Combinatorics.Expander.AffinePlane
import Complexity.Foundations.Combinatorics.Expander.Hom
import Complexity.Foundations.Combinatorics.Expander.LowerBound
import Complexity.Foundations.Combinatorics.Expander.Mixing
import Complexity.Foundations.Combinatorics.Hypergeometric
import Complexity.Foundations.Combinatorics.MajorityVote
import Complexity.Foundations.Combinatorics.PowersetTail
import Complexity.Foundations.Combinatorics.SimpleGraph.Metric
import Complexity.Foundations.Combinatorics.Sunflower.Pluck
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Concrete instances of the combinatorics toolkit

Each headline theorem of the combinatorics area is applied to a small explicit object whose
hypotheses are checked, and where possible the conclusion is compared with a direct computation:
the sunflower lemma and plucking on the edges of `K₅` and on three singletons, Valiant's depth
reduction on a path, the ball bound on the 5-cycle, the central binomial and tail bounds at
explicit sizes, and the expander mixing lemma, simple rotation maps, homomorphisms and connected
components on small rotation maps. This shows that the hypotheses are satisfiable and pins down
the counting conventions (for instance that `interedges` counts darts).
-/

namespace ComplexityTests.CombinatoricsExamples

open Cslib Finset SimpleGraph

/-! ### Sunflowers -/

-- Three edges through a common vertex are a sunflower whose core is that vertex.
private theorem isSunflower_star :
    IsSunflower ({{0, 1}, {0, 2}, {0, 3}} : Finset (Finset (Fin 5))) {0} := by
  unfold IsSunflower Set.Pairwise
  simp only [mem_coe]
  decide

-- The edges of `K₅` contain that sunflower directly and by the sunflower lemma (`10 > 8`), and
-- plucking with three petals leaves at most eight sets and no such sunflower.
example :
    ContainsSunflower 3 ((univ : Finset (Fin 5)).powersetCard 2) ∧
    (pluckNormalForm 3 ((univ : Finset (Fin 5)).powersetCard 2)).card ≤ 8 ∧
    ¬ ContainsSunflower 3 (pluckNormalForm 3 ((univ : Finset (Fin 5)).powersetCard 2)) :=
  ⟨containsSunflower_of_forall_card_le 3 2 _ (fun _ hs => (mem_powersetCard.1 hs).2.le) (by decide),
    card_pluckNormalForm_le (w := 2) (by decide) fun _ hs => (mem_powersetCard.1 hs).2.le,
    not_containsSunflower_pluckNormalForm (by decide) _⟩

-- Plucking the singletons `{0}, {1}, {2}` with two petals must end at `{∅}`: the normal form has
-- at most `sunflowerBound 2 1 = 1` set, and that set lies inside both `{0}` and `{1}`.
example :
    ContainsSunflower 3 ((univ : Finset (Fin 5)).powersetCard 2) ∧
    pluckNormalForm 2 ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) = {∅} := by
  refine ⟨⟨{{0, 1}, {0, 2}, {0, 3}}, by decide, by decide, {0}, isSunflower_star⟩, ?_⟩
  set F : Finset (Finset (Fin 3)) := {{0}, {1}, {2}}
  have hcard : (pluckNormalForm 2 F).card ≤ 1 :=
    card_pluckNormalForm_le (w := 1) le_rfl (by decide)
  obtain ⟨t, ht, ht0⟩ := exists_subset_of_mem_pluckNormalForm (p := 2) (s := {0})
    (show {0} ∈ F by decide)
  obtain ⟨u, hu, hu1⟩ := exists_subset_of_mem_pluckNormalForm (p := 2) (s := {1})
    (show {1} ∈ F by decide)
  obtain rfl : t = u := card_le_one.1 hcard t ht u hu
  obtain rfl : t = ∅ := eq_empty_of_forall_notMem fun x hx => by
    have h0 := mem_singleton.1 (ht0 hx)
    have h1 := mem_singleton.1 (hu1 hx)
    exact absurd (h0.symm.trans h1) (by decide)
  exact eq_singleton_iff_unique_mem.2 ⟨ht, fun x hx => card_le_one.1 hcard x hx ∅ ht⟩

/-! ### Valiant's depth reduction -/

/-- The directed path `0 → 1 → 2 → 3`. -/
private def pathEdges : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 2), (2, 3)}

-- Numbering the vertices grades the path with `2 ^ 2` levels.
private theorem isGrading_pathEdges : IsGrading pathEdges (2 ^ 2) fun v => v.val :=
  ⟨fun v => v.isLt, by decide⟩

-- The whole path has no grading with two levels.
private theorem not_isGrading_pathEdges (g : Fin 4 → ℕ) : ¬ IsGrading pathEdges 2 g := by
  rintro ⟨hlt, hE⟩
  have h01 := hE (0, 1) (by decide)
  have h12 := hE (1, 2) (by decide)
  have := hlt 2
  simp only at h01 h12
  omega

-- One round of depth reduction (`k = 2`, `r = 1`) removes at most `3 / 2` of the edges; since the
-- path has no two-level grading, it removes exactly one.
example : ∃ F ⊆ pathEdges, #F = 1 ∧ ∃ g : Fin 4 → ℕ, IsGrading (pathEdges \ F) 2 g := by
  obtain ⟨F, hF, hcard, g, hg⟩ := isGrading_pathEdges.exists_sdiff (r := 1) (by norm_num)
  refine ⟨F, hF, ?_, g, hg⟩
  have h3 : #pathEdges = 3 := by decide
  rcases Nat.eq_zero_or_pos #F with h | h
  · rw [card_eq_zero.1 h, sdiff_empty] at hg
    exact absurd hg (not_isGrading_pathEdges g)
  · omega

/-! ### Balls in graphs of bounded degree -/

-- In the 5-cycle, of maximum degree `2`, the closed ball of radius `1` has at most
-- `(2 + 1) ^ 1 = 3` vertices, and the ball `{4, 0, 1}` around `0` attains the bound.
example : #{v | (cycleGraph 5).edist 0 v ≤ (1 : ℕ)} = 3 := by
  refine le_antisymm (card_edist_le_le (fun _ => cycleGraph_degree_three_le.le) 0 1) ?_
  have hsub : ({0, 1, 4} : Finset (Fin 5)) ⊆
      ({v | (cycleGraph 5).edist 0 v ≤ (1 : ℕ)} : Finset (Fin 5)) := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rw [mem_filter]
    refine ⟨mem_univ v, ?_⟩
    rcases hv with rfl | rfl | rfl
    · simp
    · rw [edist_eq_one_iff_adj.2 (by decide)]
      simp
    · rw [edist_eq_one_iff_adj.2 (by decide)]
      simp
  exact le_trans (by decide : 3 ≤ #({0, 1, 4} : Finset (Fin 5))) (card_le_card hsub)

/-! ### Central binomial coefficients, hypergeometric, and binomial tails -/

-- Central binomial and tail bounds at `m = 3`, `n = 5`, `n = 99`, and hypergeometric / majority
-- vote bounds.
example :
    Nat.centralBinom 3 = 20 ∧
    Nat.centralBinom 3 ^ 2 * 7 ≤ 16 ^ 3 ∧
    Nat.choose 5 2 = 10 ∧
    Nat.choose 5 2 ^ 2 * 6 ≤ 4 ^ 5 ∧
    10 * (univ.filter fun S : Finset (Fin 99) => S.card ≤ 49).card ≤ 6 * 2 ^ 99 ∧
    ∑ J ∈ (range 4).powersetCard 2, #(range 2 ∩ J) =
      #(range 2) * (#(range 4) - 1).choose (2 - 1) ∧
    ∑ J ∈ (range 4).powersetCard 2, #(range 2 ∩ J) = 6 ∧
    2 * #{J ∈ (range 16).powersetCard 12 | #(range 12 ∩ J) < 4} ≤ Nat.choose 16 12 ∧
    #{x ∈ (range 4).powerset | #(range 3 ∩ x) ≤ 0} = 2 ∧
    2 ^ 3 * #{x ∈ (range 4).powerset | #(range 3 ∩ x) ≤ 0} ≤ 3 ^ 3 * 2 ^ 1 ∧
    (univ.filter fun ω : Fin (2 * 1) → Fin 3 =>
      (univ.filter fun i => ω i ∈ ({0, 1} : Finset (Fin 3))).card ≤ 1).card = 5 ∧
    9 ^ 1 * (univ.filter fun ω : Fin (2 * 1) → Fin 3 =>
      (univ.filter fun i => ω i ∈ ({0, 1} : Finset (Fin 3))).card ≤ 1).card ≤
      8 ^ 1 * Fintype.card (Fin 3) ^ (2 * 1) :=
  ⟨by decide, centralBinom_sq_mul_le 3,
    by decide, choose_half_sq_mul_le 5,
    by simpa using ten_mul_card_filter_card_le_le 99 0 (by norm_num),
    sum_card_inter_powersetCard (range_subset_range.2 (by norm_num)) (by norm_num),
    by decide,
    by
      simpa using two_mul_card_filter_card_inter_lt_le (s := range 16) (U := range 12) (ℓ := 12)
        (range_subset_range.2 (by norm_num)) (by simp) (by simp) (m := 4) (by simp),
    by decide,
    by
      simpa only [card_range] using
        two_pow_mul_card_filter_card_inter_le (range_subset_range.2 (by norm_num : 3 ≤ 4)) 0,
    by decide,
    card_filter_card_filter_le_le ({0, 1} : Finset (Fin 3)) (by decide) 1⟩

-- For `m ≥ 12` the bound gives `5 * C(2m, m) ≤ 4 ^ m`, since then `2m + 1 ≥ 25`.
example (m : ℕ) (hm : 12 ≤ m) : 5 * m.centralBinom ≤ 4 ^ m := by
  refine (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 ?_
  calc (5 * m.centralBinom) ^ 2 = m.centralBinom ^ 2 * 25 := by ring
    _ ≤ m.centralBinom ^ 2 * (2 * m + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 16 ^ m := centralBinom_sq_mul_le m
    _ = (4 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-! ### Rotation maps and the expander mixing lemma -/

/-- The 4-cycle as a rotation map: label `true` steps forward and arrives on label `false`. -/
private def cycleFour : RotationMap (Fin 4) Bool where
  rot p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  rot_involutive := by
    unfold Function.Involutive
    decide

private theorem isSimple_cycleFour : cycleFour.IsSimple :=
  ⟨by decide, by decide⟩

-- The simple graph of the 4-cycle is `2`-regular, one walk step averages over the two neighbors,
-- and the complete graph with loops on four vertices has `λ = 0`, so `e({0, 1}, {2}) = 2`.
example (f : Fin 4 → ℝ) :
    cycleFour.toSimpleGraph.IsRegularOfDegree 2 ∧
    cycleFour.walk f 0 = (f 1 + f 3) / 2 ∧
    #((RotationMap.complete (Fin 4)).interedges {0, 1} {2}) = 2 := by
  refine ⟨isSimple_cycleFour.isRegularOfDegree, ?_, ?_⟩
  · rw [isSimple_cycleFour.walk_apply_eq_sum_neighborFinset,
      show cycleFour.toSimpleGraph.neighborFinset 0 = {1, 3} by decide, sum_pair (by decide)]
    simp
  · have h := (RotationMap.complete (Fin 4)).abs_card_interedges_sub_le {0, 1} {2}
    rw [RotationMap.spectralExpansion_complete, zero_mul, zero_mul, zero_div,
      abs_nonpos_iff, sub_eq_zero] at h
    have h' : (#((RotationMap.complete (Fin 4)).interedges {0, 1} {2}) : ℝ) = 2 := by
      rw [h]
      simp
    exact_mod_cast h'

-- The affine plane over `ZMod 3` (nine vertices, degree three) has `λ ≤ √(1 / 3) < 1`, so every
-- nonempty set of at most four vertices has an edge leaving it.
example (S : Finset (ZMod 3 × ZMod 3)) (hS : S.Nonempty) (hS4 : 2 * #S ≤ 9) :
    0 < #((RotationMap.affinePlane (ZMod 3)).interedges S Sᶜ) := by
  have hcard : Fintype.card (ZMod 3 × ZMod 3) = 9 := by simp [ZMod.card]
  have h := (RotationMap.affinePlane (ZMod 3)).le_card_interedges_compl_of_two_mul_card_le
    (S := S) (hcard ▸ hS4)
  have hlam : (RotationMap.affinePlane (ZMod 3)).spectralExpansion < 1 := by
    refine (RotationMap.spectralExpansion_affinePlane_le (K := ZMod 3)).trans_lt ?_
    rw [Real.sqrt_lt' one_pos]
    simp only [ZMod.card, Nat.cast_ofNat, one_div, one_pow]
    norm_num
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hpos : (0 : ℝ) < (1 - (RotationMap.affinePlane (ZMod 3)).spectralExpansion) *
      Fintype.card (ZMod 3) * #S / 2 := by
    have : (0 : ℝ) < Fintype.card (ZMod 3) := by simp [ZMod.card]
    have : (0 : ℝ) < 1 - (RotationMap.affinePlane (ZMod 3)).spectralExpansion := by linarith
    positivity
  exact_mod_cast hpos.trans_le h

/-- The 2-cycle, with both edges joining `0` and `1`. -/
private def cycleTwo : RotationMap (Fin 2) Bool where
  rot p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  rot_involutive := by
    unfold Function.Involutive
    decide

/-- Reducing the 4-cycle modulo two is a homomorphism onto the 2-cycle. -/
private def modTwo : RotationMap.Hom cycleFour cycleTwo where
  toFun v := if v.val % 2 = 0 then 0 else 1
  rot_map' := by decide

-- Walks lift along the homomorphism: `1` is reachable from the image of `0`, so some vertex
-- reachable from `0` in the 4-cycle maps to `1`.
example : ∃ v, cycleFour.toSimpleGraph.Reachable 0 v ∧ modTwo v = 1 :=
  modTwo.exists_reachable_apply_eq (u := 0) (Adj.reachable ⟨by decide, true, by decide⟩)

/-- Two disjoint edges, `0 — 1` and `2 — 3`. -/
private def twoEdges : RotationMap (Fin 4) Unit :=
  RotationMap.ofInvolutive ![1, 0, 3, 2] (by unfold Function.Involutive; decide)

-- `{0, 1}` is closed under taking neighbors, so `2` is not reachable from `0`: the graph is
-- disconnected, but the connected component of `0` is connected.
example : ¬ twoEdges.toSimpleGraph.Preconnected ∧
    (twoEdges.componentGraph 0).toSimpleGraph.Preconnected := by
  refine ⟨fun h => ?_, twoEdges.preconnected_componentGraph 0⟩
  have hS : ∀ v ∈ ({0, 1} : Set (Fin 4)), ∀ i, twoEdges.neighbor v i ∈ ({0, 1} : Set (Fin 4)) := by
    rintro v (rfl | rfl) i <;> simp [twoEdges]
  have := twoEdges.mem_of_reachable hS (by simp) (h 0 2)
  simp at this

end ComplexityTests.CombinatoricsExamples
