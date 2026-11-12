/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Trial
import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.Data.Nat.LargePrimeDivisors
import CslibFrontier.Foundations.NumberTheory.PrimeDensity
import Mathlib.Tactic.LinearCombination

/-!
# The success probability of a hashing trial

The error analysis of [ChanItakuraMaYu2026], Theorem 2.3, for a fixed prime `p`, as counts over
the uniform seeds `seeds p`: the triples `(ξ, α, β) ∈ ZMod p ^ 3` with `ξ ≠ 0`, of which there are
`(p - 1) p ^ 2` (`card_seeds`).

* Two hash values are hit by `p - 1` seeds (`card_seeds_left_right`): for fixed `ξ` there is one
  `α` and one `β`.
* Three hash values, two of them left hashes of different residues, are hit by at most one seed
  (`card_seeds_left_right_left_le`).
* **Per-trial bound** (`card_accepts_add_ge`): suppose `c = a + b` with `a`, `b` isolated
  (not in `A_bad`, `B_bad`) and `2 ^ d ≤ p`. Let `L` be the pairs of the trial's inputs whose sum
  is congruent to `c` modulo `p` but different from `c` (`falsePairs`), and `P` the ordered pairs of
  disjoint `t`-sets of `[d]`, as numbers (`rankedPairs`). Then
  `#accepting seeds + #P · #L · (2 t choose t) ≥ #P · (p - 1)`.
  This is inequality (1)–(2) of the paper without its `Õ` and with explicit counts. With the
  paper's goodness condition `4 #L (2 t choose t) ≤ p - 1`, a trial accepts with probability at
  least `(3/4) #P / p ^ 2` (`four_mul_card_accepts_ge`), and
  `#P = (d choose 2 t) (2 t choose t)` (`card_rankedPairs`).
* **Independent trials** (`card_forall_not_accepts`): `μ` independent uniform seeds all reject
  with probability `(1 - q) ^ μ` for the success probability `q` of one trial.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.seeds`: the uniform seeds.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.rankedPairs`, `falsePairs`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_accepts_add_ge`,
  `four_mul_card_accepts_ge`: the success probability of one trial.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_rankedPairs`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_forall_not_accepts`: independent trials.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib.Algorithms.Lean.Yates

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- The seeds of one trial, uniformly distributed: `ξ ≠ 0`, `α` and `β` arbitrary. -/
@[expose] def seeds (p : ℕ) [NeZero p] : Finset (Seed p) := univ.filter fun s => s.ξ ≠ 0

@[simp] theorem mem_seeds {s : Seed p} : s ∈ seeds p ↔ s.ξ ≠ 0 := by
  unfold seeds; exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩

private theorem card_ne_zero_zmod : #(univ.filter fun ξ : ZMod p => ξ ≠ 0) = p - 1 := by
  rw [filter_ne' univ (0 : ZMod p), card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

theorem card_seeds : #(seeds p) = (p - 1) * p ^ 2 := by
  have h : #(seeds p) = #((univ.filter fun ξ : ZMod p => ξ ≠ 0) ×ˢ
      ((univ : Finset (ZMod p)) ×ˢ (univ : Finset (ZMod p)))) := by
    refine card_bij' (fun s _ => (s.ξ, s.α, s.β)) (fun x _ => ⟨x.1, x.2.1, x.2.2⟩) ?_ ?_ ?_ ?_
    · intro s hs; simpa using hs
    · intro x hx; simpa using hx
    · intro s _; rfl
    · intro x _; rfl
  rw [h, card_product, card_product, card_ne_zero_zmod, card_univ, ZMod.card]
  ring

private theorem eq_natCast_of_val_eq {z : ZMod p} {x : ℕ} (h : z.val = x) : z = x := by
  rw [← h, ZMod.natCast_zmod_val]

/-- **Two hash values** `f a = x`, `g b = y` below `p` are hit by exactly `p - 1` seeds. -/
theorem card_seeds_left_right (a b : ℕ) {x y : ℕ} (hx : x < p) (hy : y < p) :
    #((seeds p).filter fun s => s.left a = x ∧ s.right b = y) = p - 1 := by
  rw [← card_ne_zero_zmod]
  refine card_bij' (fun s _ => s.ξ) (fun ξ _ => ⟨ξ, x - a * ξ, y - b * ξ⟩) ?_ ?_ ?_ ?_
  · intro s hs
    exact mem_filter.mpr ⟨mem_univ _, mem_seeds.mp (mem_filter.mp hs).1⟩
  · intro ξ hξ
    replace hξ := (mem_filter.mp hξ).2
    refine mem_filter.mpr ⟨mem_seeds.mpr hξ, ?_, ?_⟩ <;>
      simp only [Seed.left, Seed.right, add_sub_cancel, ZMod.val_natCast_of_lt hx,
        ZMod.val_natCast_of_lt hy]
  · intro s hs
    replace hs := (mem_filter.mp hs).2
    simp only [Seed.left, Seed.right] at hs
    have hα := eq_natCast_of_val_eq hs.1
    have hβ := eq_natCast_of_val_eq hs.2
    obtain ⟨ξ, α, β⟩ := s
    simp only at hα hβ ⊢
    rw [Seed.mk.injEq]
    exact ⟨rfl, by linear_combination (-1 : ZMod p) * hα, by linear_combination (-1 : ZMod p) * hβ⟩
  · intro ξ _
    rfl

/-- **Three hash values**, two of them left hashes of elements in different residue classes, are
hit by at most one seed. -/
theorem card_seeds_left_right_left_le {a a' : ℕ} (ha : (a : ZMod p) ≠ a') (b x y z : ℕ) :
    #((seeds p).filter fun s => s.left a = x ∧ s.right b = y ∧ s.left a' = z) ≤ 1 := by
  refine card_le_one.mpr fun s hs s' hs' => ?_
  obtain ⟨h1, h2, h3⟩ := (mem_filter.mp hs).2
  obtain ⟨h1', h2', h3'⟩ := (mem_filter.mp hs').2
  simp only [Seed.left, Seed.right] at h1 h2 h3 h1' h2' h3'
  have e1 := eq_natCast_of_val_eq h1
  have e2 := eq_natCast_of_val_eq h2
  have e3 := eq_natCast_of_val_eq h3
  have e1' := eq_natCast_of_val_eq h1'
  have e2' := eq_natCast_of_val_eq h2'
  have e3' := eq_natCast_of_val_eq h3'
  obtain ⟨ξ, α, β⟩ := s
  obtain ⟨ξ', α', β'⟩ := s'
  simp only at e1 e2 e3 e1' e2' e3'
  have hξ : ξ = ξ' := by
    have : ((a : ZMod p) - a') * (ξ - ξ') = 0 := by linear_combination e1 - e3 - e1' + e3'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) ha
    · exact sub_eq_zero.mp h
  subst hξ
  rw [Seed.mk.injEq]
  exact ⟨rfl, by linear_combination e1 - e1', by linear_combination e2 - e2'⟩

/-! ### The success probability of one trial -/

/-- The ordered pairs of numbers below `2 ^ d` whose sets are disjoint `t`-sets. -/
@[expose] def rankedPairs (d t : ℕ) : Finset (ℕ × ℕ) :=
  (range (2 ^ d) ×ˢ range (2 ^ d)).filter fun xy =>
    Ranked d t xy.1 ∧ Ranked d t xy.2 ∧ Disjoint (maskSet d xy.1) (maskSet d xy.2)

/-- The pairs of `A × B` whose sum is congruent to `c` modulo `p` but different from `c`: the
paper's `L`. -/
@[expose] def falsePairs (p : ℕ) (c : ℕ) (A B : List ℕ) : Finset (ℕ × ℕ) :=
  (A.toFinset ×ˢ B.toFinset).filter fun ab => ((ab.1 + ab.2 : ℕ) : ZMod p) = c ∧ ab.1 + ab.2 ≠ c

/-- The numbers whose sets are `t`-subsets of the union of the sets of `x` and `y`. -/
@[expose] def candidates (d t x y : ℕ) : Finset ℕ :=
  ((maskSet d x ∪ maskSet d y).powersetCard t).image fun S => (maskIndex S : ℕ)

theorem card_candidates_le {d t x y : ℕ} (hx : Ranked d t x) (hy : Ranked d t y)
    (hxy : Disjoint (maskSet d x) (maskSet d y)) : #(candidates d t x y) ≤ (2 * t).choose t := by
  refine card_image_le.trans ?_
  rw [card_powersetCard, card_union_of_disjoint hxy, hx.2, hy.2, two_mul]

/-- A false pair is not in the residue class of an isolated witness. -/
theorem natCast_ne_of_mem_falsePairs {A B Ag Bg : List ℕ} (hAg : ∀ x ∈ Ag, x ∈ A)
    (hBg : ∀ x ∈ Bg, x ∈ B) {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (hia : Isolated p A a)
    (hib : Isolated p B b) (habc : a + b = c) {ab : ℕ × ℕ} (hab : ab ∈ falsePairs p c Ag Bg) :
    (a : ZMod p) ≠ ab.1 := by
  obtain ⟨hmem, hcong, hne⟩ := mem_filter.mp hab
  obtain ⟨ha', hb'⟩ := mem_product.mp hmem
  intro h
  have e1 : ab.1 = a := hia.eq ha (hAg _ (List.mem_toFinset.mp ha')) h.symm
  have e2 : ab.2 = b := hib.eq hb (hBg _ (List.mem_toFinset.mp hb')) (by
    have : ((ab.1 + ab.2 : ℕ) : ZMod p) = ((a + b : ℕ) : ZMod p) := by rw [hcong, habc]
    push_cast at this
    rw [e1] at this
    exact add_left_cancel this)
  exact hne (by rw [e1, e2, habc])

/-- **The success count of one trial** ([ChanItakuraMaYu2026], Theorem 2.3, inequalities (1) and
(2)): if `c = a + b` with `a ∈ Ag ⊆ A` and `b ∈ Bg ⊆ B` isolated in `A` and `B`, and
`2 ^ d ≤ p`, then
`#rankedPairs · (p - 1) ≤ #accepting seeds + #rankedPairs · #L · (2 t choose t)`. -/
theorem card_accepts_add_ge {d t : ℕ} (hp : 2 ^ d ≤ p) {A B Ag Bg : List ℕ}
    (hAg : ∀ x ∈ Ag, x ∈ A) (hBg : ∀ x ∈ Bg, x ∈ B) {a b c : ℕ} (ha : a ∈ Ag) (hb : b ∈ Bg)
    (hia : Isolated p A a) (hib : Isolated p B b) (habc : a + b = c) :
    #(rankedPairs d t) * (p - 1) ≤ #((seeds p).filter fun s => Accepts d t s Ag Bg c) +
      #(rankedPairs d t) * (#(falsePairs p c Ag Bg) * (2 * t).choose t) := by
  set P := rankedPairs d t
  set L := falsePairs p c Ag Bg
  let E : ℕ × ℕ → Finset (Seed p) := fun xy =>
    (seeds p).filter fun s => s.left a = xy.1 ∧ s.right b = xy.2
  have hE : ∀ xy ∈ P, #(E xy) = p - 1 := fun xy hxy => by
    obtain ⟨hmem, -⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hmem
    exact card_seeds_left_right a b ((mem_range.mp hx).trans_le hp) ((mem_range.mp hy).trans_le hp)
  -- the rejecting seeds of a pair of hash values are covered by the false pairs
  have hBad : ∀ xy ∈ P, #((E xy).filter fun s => ¬ Accepts d t s Ag Bg c) ≤
      #L * (2 * t).choose t := by
    intro xy hxy
    obtain ⟨-, hx, hy, hxy'⟩ := mem_filter.mp hxy
    have hsub : (E xy).filter (fun s => ¬ Accepts d t s Ag Bg c) ⊆ L.biUnion fun ab =>
        (candidates d t xy.1 xy.2).biUnion fun z =>
          (seeds p).filter fun s => s.left a = xy.1 ∧ s.right b = xy.2 ∧ s.left ab.1 = z := by
      intro s hs
      obtain ⟨hsE, hrej⟩ := mem_filter.mp hs
      obtain ⟨hseed, hfa, hgb⟩ := mem_filter.mp hsE
      have hξ := mem_seeds.mp hseed
      rw [← hfa] at hx hxy'
      rw [← hgb] at hy hxy'
      obtain hacc | ⟨a', ha', b', hb', hcov, hne⟩ :=
        accepts_or_exists_covers_ne hp ha hb habc hx hy hxy'
      · exact absurd hacc hrej
      have hrA := (by simpa using (List.mem_filter.mp ha').2 : Ranked d t (s.left a'))
      have hrB := (by simpa using (List.mem_filter.mp hb').2 : Ranked d t (s.right b'))
      obtain ⟨hlt, hmask⟩ := maskSet_add hx.1 hy.1 hxy'
      have htarget := target_eq_add (s := s) habc (hlt.trans_le hp)
      have hcong := natCast_add_eq_of_covers hξ hrA.1 hrB.1 (htarget ▸ hlt) hcov
      refine mem_biUnion.mpr ⟨(a', b'), ?_, mem_biUnion.mpr ⟨s.left a', ?_, ?_⟩⟩
      · exact mem_filter.mpr ⟨mem_product.mpr ⟨List.mem_toFinset.mpr (List.mem_of_mem_filter ha'),
          List.mem_toFinset.mpr (List.mem_of_mem_filter hb')⟩, hcong, hne⟩
      · refine mem_image.mpr ⟨maskSet d (s.left a'), mem_powersetCard.mpr ⟨?_, hrA.2⟩, ?_⟩
        · have h1 : maskSet d (s.left a') ⊆ maskSet d (s.target c) := by
            rw [← hcov.2]; exact subset_union_left
          rw [htarget, hmask] at h1
          simpa [hfa, hgb] using h1
        · exact congrArg Fin.val (maskIndex_maskSet ⟨_, hrA.1⟩)
      · exact mem_filter.mpr ⟨hseed, hfa, hgb, rfl⟩
    refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
    rw [← smul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun ab hab => (card_biUnion_le).trans ?_
    refine (sum_le_card_nsmul _ _ 1 fun z _ => card_seeds_left_right_left_le
      (natCast_ne_of_mem_falsePairs hAg hBg (hAg a ha) (hBg b hb) hia hib habc hab) _ _ _ _).trans
      ?_
    simpa using card_candidates_le hx hy hxy'
  have hsplit : ∀ xy ∈ P, p - 1 ≤ #((E xy).filter fun s => Accepts d t s Ag Bg c) +
      #L * (2 * t).choose t := by
    intro xy hxy
    rw [← hE xy hxy, ← card_filter_add_card_filter_not (s := E xy) (fun s => Accepts d t s Ag Bg c)]
    exact Nat.add_le_add_left (hBad xy hxy) _
  have hdisj : (P : Set (ℕ × ℕ)).PairwiseDisjoint fun xy =>
      (E xy).filter fun s => Accepts d t s Ag Bg c := by
    intro xy _ xy' _ hne
    refine disjoint_left.mpr fun s hs hs' => hne ?_
    obtain ⟨-, h1, h2⟩ := mem_filter.mp (mem_filter.mp hs).1
    obtain ⟨-, h1', h2'⟩ := mem_filter.mp (mem_filter.mp hs').1
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')
  have hunion : P.biUnion (fun xy => (E xy).filter fun s => Accepts d t s Ag Bg c) ⊆
      (seeds p).filter fun s => Accepts d t s Ag Bg c := by
    intro s hs
    obtain ⟨xy, -, hs⟩ := mem_biUnion.mp hs
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hs).1).1, (mem_filter.mp hs).2⟩
  calc #P * (p - 1) = ∑ _xy ∈ P, (p - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ xy ∈ P, (#((E xy).filter fun s => Accepts d t s Ag Bg c) + #L * (2 * t).choose t) :=
        sum_le_sum hsplit
    _ = #(P.biUnion fun xy => (E xy).filter fun s => Accepts d t s Ag Bg c) +
          #P * (#L * (2 * t).choose t) := by
        rw [sum_add_distrib, card_biUnion hdisj, sum_const, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right (card_le_card hunion) _

/-- **A good prime** ([ChanItakuraMaYu2026], inequality (2)): if moreover
`4 #L (2 t choose t) ≤ p - 1`, a trial accepts `c` with probability at least `(3/4) #P / p ^ 2`,
that is, `3 #P (p - 1) ≤ 4 #accepting seeds`. -/
theorem four_mul_card_accepts_ge {d t : ℕ} (hp : 2 ^ d ≤ p) {A B Ag Bg : List ℕ}
    (hAg : ∀ x ∈ Ag, x ∈ A) (hBg : ∀ x ∈ Bg, x ∈ B) {a b c : ℕ} (ha : a ∈ Ag) (hb : b ∈ Bg)
    (hia : Isolated p A a) (hib : Isolated p B b) (habc : a + b = c)
    (hgood : 4 * (#(falsePairs p c Ag Bg) * (2 * t).choose t) ≤ p - 1) :
    3 * (#(rankedPairs d t) * (p - 1)) ≤
      4 * #((seeds p).filter fun s => Accepts d t s Ag Bg c) := by
  have h := card_accepts_add_ge (d := d) (t := t) hp hAg hBg ha hb hia hib habc
  have h2 : 4 * (#(rankedPairs d t) * (#(falsePairs p c Ag Bg) * (2 * t).choose t)) ≤
      #(rankedPairs d t) * (p - 1) := by
    calc _ = #(rankedPairs d t) * (4 * (#(falsePairs p c Ag Bg) * (2 * t).choose t)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hgood
  omega

/-- The ordered pairs of disjoint `t`-sets of `[d]`: `(d choose 2 t) (2 t choose t)`. -/
theorem card_rankedPairs (d t : ℕ) : #(rankedPairs d t) = d.choose (2 * t) * (2 * t).choose t := by
  have h : #(rankedPairs d t) =
      #(((univ : Finset (Fin d)).powersetCard (2 * t)).sigma fun Z => Z.powersetCard t) := by
    refine card_bij' (fun xy _ => ⟨maskSet d xy.1 ∪ maskSet d xy.2, maskSet d xy.1⟩)
      (fun Zx _ => ((maskIndex Zx.2 : ℕ), (maskIndex (Zx.1 \ Zx.2) : ℕ))) ?_ ?_ ?_ ?_
    · intro xy hxy
      obtain ⟨-, hx, hy, hd⟩ := mem_filter.mp hxy
      refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩,
        mem_powersetCard.mpr ⟨subset_union_left, hx.2⟩⟩
      rw [card_union_of_disjoint hd, hx.2, hy.2, two_mul]
    · intro Zx hZx
      obtain ⟨hZ, hx⟩ := mem_sigma.mp hZx
      obtain ⟨-, hZc⟩ := mem_powersetCard.mp hZ
      obtain ⟨hxZ, hxc⟩ := mem_powersetCard.mp hx
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (maskIndex _).isLt,
        mem_range.mpr (maskIndex _).isLt⟩, ⟨(maskIndex _).isLt, ?_⟩, ⟨(maskIndex _).isLt, ?_⟩, ?_⟩
      · rw [show maskSet d (maskIndex Zx.2 : ℕ) = Zx.2 from maskSet_maskIndex _, hxc]
      · rw [show maskSet d (maskIndex (Zx.1 \ Zx.2) : ℕ) = Zx.1 \ Zx.2 from maskSet_maskIndex _,
          card_sdiff_of_subset hxZ, hZc, hxc]
        omega
      · rw [show maskSet d (maskIndex Zx.2 : ℕ) = Zx.2 from maskSet_maskIndex _,
          show maskSet d (maskIndex (Zx.1 \ Zx.2) : ℕ) = Zx.1 \ Zx.2 from maskSet_maskIndex _]
        exact disjoint_sdiff
    · intro xy hxy
      obtain ⟨-, hx, hy, hd⟩ := mem_filter.mp hxy
      simp only [union_sdiff_cancel_left hd]
      exact Prod.ext (congrArg Fin.val (maskIndex_maskSet ⟨_, hx.1⟩))
        (congrArg Fin.val (maskIndex_maskSet ⟨_, hy.1⟩))
    · intro Zx hZx
      obtain ⟨hZ, hx⟩ := mem_sigma.mp hZx
      obtain ⟨hxZ, -⟩ := mem_powersetCard.mp hx
      simp only [show maskSet d (maskIndex Zx.2 : ℕ) = Zx.2 from maskSet_maskIndex _,
        show maskSet d (maskIndex (Zx.1 \ Zx.2) : ℕ) = Zx.1 \ Zx.2 from maskSet_maskIndex _,
        union_sdiff_of_subset hxZ]
  rw [h, card_sigma, sum_congr rfl fun Z hZ => by
    rw [card_powersetCard, (mem_powersetCard.mp hZ).2], sum_const, card_powersetCard, card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Independent trials**: the tuples of `μ` seeds that all reject `c` are the `μ`-th power of the
rejecting seeds, so `μ` independent uniform trials all reject with probability `(1 - q) ^ μ`. -/
theorem card_forall_not_accepts (d t μ : ℕ) (Ag Bg : List ℕ) (c : ℕ) :
    #((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        ∀ i, ¬ Accepts d t (ss i) Ag Bg c) =
      #((seeds p).filter fun s => ¬ Accepts d t s Ag Bg c) ^ μ := by
  rw [← Fintype.card_piFinset_const]
  congr 1
  ext ss
  simp only [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-! ### The random prime -/

/-- The primes of `[2 ^ d, 2 ^ (d + 1))`. For `d ≥ 2` these are the primes of `(p₀, 2 p₀]` with
`p₀ = 2 ^ d`, from which [ChanItakuraMaYu2026], Theorem 2.3, draws `p`. -/
@[expose] def primeWindow (d : ℕ) : Finset ℕ := (Ico (2 ^ d) (2 ^ (d + 1))).filter Nat.Prime

theorem mem_primeWindow {d q : ℕ} : q ∈ primeWindow d ↔ q.Prime ∧ 2 ^ d ≤ q ∧ q < 2 ^ (d + 1) := by
  simp only [primeWindow, mem_filter, mem_Ico]
  tauto

/-- At least a `1 / (3 (d + 1))` fraction of `[2 ^ d, 2 ^ (d + 1))` is prime
([KatzLindell2020], Theorem 9.32, as `Nat.two_pow_sub_one_le_three_mul_card_primes`). -/
theorem two_pow_le_card_primeWindow {d : ℕ} (hd : 1 ≤ d) :
    2 ^ d ≤ 3 * (d + 1) * #(primeWindow d) := by
  have := Nat.two_pow_sub_one_le_three_mul_card_primes (n := d + 1) (by omega)
  simpa [primeWindow] using this

/-- A pair is false modulo `q` exactly when `q` divides the nonzero difference of its sum and
`c`. -/
theorem mem_falsePairs_iff {q c : ℕ} {A B : List ℕ} {ab : ℕ × ℕ} :
    ab ∈ falsePairs q c A B ↔ ab ∈ A.toFinset ×ˢ B.toFinset ∧ ab.1 + ab.2 ≠ c ∧
      q ∣ (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs := by
  simp only [falsePairs, mem_filter]
  have : (((ab.1 + ab.2 : ℕ) : ZMod q) = c) ↔ q ∣ (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs, ← dvd_neg, neg_sub,
      ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast; rfl
  rw [this]
  tauto

/-- **The false pairs over all primes of the window** are few: each pair whose sum differs from
`c` by at most `M` is false for at most `log₂ M / d` primes of the window. -/
theorem mul_sum_card_falsePairs_le {d c M : ℕ} {A B : List ℕ}
    (hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ M) :
    d * ∑ q ∈ primeWindow d, #(falsePairs q c A B) ≤
      #(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M := by
  set S := (A.toFinset ×ˢ B.toFinset).filter fun ab => ab.1 + ab.2 ≠ c
  have hfp : ∀ q, falsePairs q c A B =
      S.filter fun ab => q ∣ (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs := fun q => by
    ext ab
    rw [mem_falsePairs_iff, mem_filter, mem_filter]
    tauto
  have hswap : ∑ q ∈ primeWindow d, #(falsePairs q c A B) =
      ∑ ab ∈ S, #((primeWindow d).filter (· ∣ (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs)) := by
    simp only [hfp, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [hswap, mul_sum]
  calc ∑ ab ∈ S, d * #((primeWindow d).filter (· ∣ (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs))
      ≤ ∑ _ab ∈ S, Nat.log 2 M := sum_le_sum fun ab hab => by
        obtain ⟨hmem, hne⟩ := mem_filter.mp hab
        have hz : (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≠ 0 := by
          rw [Int.natAbs_ne_zero, sub_ne_zero]; exact_mod_cast hne
        rw [mul_comm]
        exact (Nat.card_filter_dvd_mul_le_log (fun q hq => ⟨(mem_primeWindow.mp hq).1,
          (mem_primeWindow.mp hq).2.1⟩) hz).trans (Nat.log_mono_right (hM ab hmem))
    _ ≤ #(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_filter_le _ _)

/-- The primes of the window that are not good for `c`: `p - 1 < 4 #L (2 t choose t)`. -/
@[expose] def badPrimes (d t c : ℕ) (A B : List ℕ) : Finset ℕ :=
  (primeWindow d).filter fun q => q - 1 < 4 * (#(falsePairs q c A B) * (2 * t).choose t)

/-- **Few bad primes** (Markov's inequality, as in [ChanItakuraMaYu2026], Theorem 2.3):
`d #bad (2 ^ d - 1) ≤ 4 (2 t choose t) |A| |B| log₂ M`. -/
theorem card_badPrimes_le {d t c M : ℕ} {A B : List ℕ}
    (hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ M) :
    d * (#(badPrimes d t c A B) * (2 ^ d - 1)) ≤
      4 * (2 * t).choose t * (#(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M) := by
  have h1 : #(badPrimes d t c A B) * (2 ^ d - 1) ≤
      4 * (2 * t).choose t * ∑ q ∈ primeWindow d, #(falsePairs q c A B) := by
    calc #(badPrimes d t c A B) * (2 ^ d - 1) = ∑ _q ∈ badPrimes d t c A B, (2 ^ d - 1) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ q ∈ badPrimes d t c A B, 4 * (2 * t).choose t * #(falsePairs q c A B) :=
          sum_le_sum fun q hq => by
            obtain ⟨hw, hlt⟩ := mem_filter.mp hq
            have := (mem_primeWindow.mp hw).2.1
            calc 2 ^ d - 1 ≤ q - 1 := by omega
              _ ≤ _ := by
                have := hlt.le
                calc q - 1 ≤ 4 * (#(falsePairs q c A B) * (2 * t).choose t) := this
                  _ = _ := by ring
      _ ≤ ∑ q ∈ primeWindow d, 4 * (2 * t).choose t * #(falsePairs q c A B) :=
          sum_le_sum_of_subset (filter_subset _ _)
      _ = _ := by rw [mul_sum]
  calc d * (#(badPrimes d t c A B) * (2 ^ d - 1))
      ≤ d * (4 * (2 * t).choose t * ∑ q ∈ primeWindow d, #(falsePairs q c A B)) :=
        Nat.mul_le_mul_left _ h1
    _ = 4 * (2 * t).choose t * (d * ∑ q ∈ primeWindow d, #(falsePairs q c A B)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (mul_sum_card_falsePairs_le hM)

end Cslib.Algorithms.Lean.SubsetConvThreeSum
