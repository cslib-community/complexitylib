/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.HardnessAmplification
public import Complexity.Crypto.Primitives.PRG.NisanWigderson.Circuit
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Sampling
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Nisan–Wigderson generator for derandomization

Derandomizing a polynomial-time algorithm with the Nisan–Wigderson generator
[NisanWigderson1994] needs two ingredients beyond the reconstruction of
`Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt`.

**Designs with seeds of linear length.** The algorithm runs over all `2 ^ ℓ` seeds, so the seed
length `ℓ` must be logarithmic in the running time, hence linear in the input length `n` of the
hard function. The polynomial designs of `Cslib.Crypto.PRG.NisanWigderson.Design.polynomial` have
`ℓ = n ^ 2`. Here designs are built greedily [Arora and Barak, Chapter 20][AroraBarak09], as
masks: lists of `ℓ` bits, the block of a mask being the set of positions where it is `true`.
`greedyMasks ℓ n a` runs through all masks of length `ℓ` in the order of
`Cslib.BitString.enumList` and keeps a mask when it has `n` ones and shares at most `a` of them
with every mask kept before. The result is maximal: every mask with `n` ones shares more than `a`
of them with some kept mask. Counting the `n`-sets that share `a + 1` elements with a given block
shows that the greedy design has at least `C(ℓ, a + 1) / C(n, a + 1) ^ 2` blocks
(`choose_le_length_greedyMasks_mul`), so with `ℓ = (b + 1) t` and `a + 1 = t` it has at least
`b ^ t / 4 ^ n` blocks (`le_length_greedyMasks`). The construction is a simple loop over lists,
whose running time is polynomial in `2 ^ ℓ`, and so is the generator on lists `listGenerator`,
which reads the bits of the seed at the ones of each mask (`restrictMask`) and applies the hard
function; its polynomial-time certificates are in
`Complexity/Computability/Complexity/Classes/BPP/Derandomization/Generator.lean`.

**Fooling in counting form.** For an average-case hard function `f`
(`Cslib.Circuits.Boolean.IsAverageCaseHard`), the fraction of seeds on which a small test accepts
the output of the generator is within `ε` of the fraction of all strings it accepts
(`abs_card_div_sub_card_div_lt`). The hardness hypothesis is non-strict, as produced by Yao's XOR
lemma, and the strict bound needed by the reconstruction comes from the slack `m < ε s` between
the number `m` of output bits and the hardness `s`.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.overlapCount`, `Cslib.Crypto.PRG.NisanWigderson.maskBlock`,
  `Cslib.Crypto.PRG.NisanWigderson.restrictMask`: the common ones of two masks, the block of a
  mask, and the bits of a string at the ones of a mask.
* `Cslib.Crypto.PRG.NisanWigderson.Design.ofMasks`: the design whose blocks are given by masks.
* `Cslib.Crypto.PRG.NisanWigderson.greedyMasks`: the greedy design, as a list of masks.
* `Cslib.Crypto.PRG.NisanWigderson.Design.greedy`: its first `m` blocks, as a design.
* `Cslib.Crypto.PRG.NisanWigderson.listGenerator`: the generator on lists, for a function on words
  and a list of masks.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.ofFn_restrict_ofMasks`: reading a block of a design given by
  masks is `restrictMask`.
* `Cslib.Crypto.PRG.NisanWigderson.exists_mem_greedyMasks_lt_overlapCount`: the greedy design is
  maximal.
* `Cslib.Crypto.PRG.NisanWigderson.choose_le_length_greedyMasks_mul`,
  `Cslib.Crypto.PRG.NisanWigderson.le_length_greedyMasks`: the greedy design is large.
* `Cslib.Crypto.PRG.NisanWigderson.listGenerator_take_greedyMasks`: with the greedy masks, the
  generator on lists is the Nisan–Wigderson generator of `Design.greedy`.
* `Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt`: for an average-case hard
  function, the generator fools small circuits, as a statement about counts.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Probability.PMF Finset

variable {ℓ n a m : ℕ}

/-! ### Masks -/

/-- The number of positions where both `v` and `w` are `true`. -/
def overlapCount (v w : List Bool) : ℕ :=
  (v.zipWith (· && ·) w).count true

/-- The block of positions in `Fin ℓ` where the mask `w` is `true`. -/
def maskBlock (ℓ : ℕ) (w : List Bool) : Finset (Fin ℓ) :=
  {k | w.getD k false = true}

/-- The bits of `z` at the positions where the mask `w` is `true`, in increasing order of
position. -/
def restrictMask (w z : List Bool) : List Bool :=
  ((List.range w.length).filter fun k => w.getD k false).map fun k => z.getD k false

@[simp]
theorem mem_maskBlock {w : List Bool} {k : Fin ℓ} : k ∈ maskBlock ℓ w ↔ w.getD k false = true := by
  simp [maskBlock]

/-- The ones of a mask are the elements of its block. -/
theorem count_true_eq_card_maskBlock : ∀ w : List Bool, w.count true = #(maskBlock w.length w)
  | [] => rfl
  | b :: w => by
    rw [maskBlock, List.length_cons, Fin.card_filter_univ_succ, List.count_cons,
      count_true_eq_card_maskBlock w, maskBlock]
    cases b <;> simp

/-- The ones of a mask of length `ℓ` are the elements of its block in `Fin ℓ`. -/
theorem count_true_eq_card_maskBlock_of_length {w : List Bool} (h : w.length = ℓ) :
    w.count true = #(maskBlock ℓ w) := by
  subst h
  exact count_true_eq_card_maskBlock w

/-- Two masks of length `ℓ` have as many common ones as their blocks have common elements. -/
theorem overlapCount_eq_card_inter {v w : List Bool} (hv : v.length = ℓ) (hw : w.length = ℓ) :
    overlapCount v w = #(maskBlock ℓ v ∩ maskBlock ℓ w) := by
  have hlen : (v.zipWith (· && ·) w).length = ℓ := by simp [hv, hw]
  rw [overlapCount, count_true_eq_card_maskBlock_of_length hlen]
  congr 1
  ext k
  have hkv : (k : ℕ) < v.length := hv ▸ k.isLt
  have hkw : (k : ℕ) < w.length := hw ▸ k.isLt
  have hkz : (k : ℕ) < (v.zipWith (· && ·) w).length := hlen ▸ k.isLt
  simp only [mem_maskBlock, mem_inter, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkv,
    List.getElem?_eq_getElem hkw, List.getElem?_eq_getElem hkz, Option.getD_some,
    List.getElem_zipWith, Bool.and_eq_true]

/-- A mask shares all its ones with itself. -/
theorem overlapCount_self (w : List Bool) : overlapCount w w = w.count true := by
  simp [overlapCount, List.zipWith_self]

/-- Sharing ones is symmetric. -/
theorem overlapCount_comm (v w : List Bool) : overlapCount v w = overlapCount w v := by
  rw [overlapCount, overlapCount, List.zipWith_comm]
  simp only [Bool.and_comm]

/-! ### Designs given by masks -/

/-- The design whose `i`-th block is the block of the mask `masks i`, for masks of length `ℓ` with
`n` ones each, any two of which share at most `a` ones. -/
def Design.ofMasks (masks : Fin m → List Bool) (length_masks : ∀ i, (masks i).length = ℓ)
    (count_masks : ∀ i, (masks i).count true = n)
    (overlapCount_masks : ∀ i j, i ≠ j → overlapCount (masks i) (masks j) ≤ a) :
    Design ℓ n a m where
  block i := maskBlock ℓ (masks i)
  card_block i := by
    rw [← count_true_eq_card_maskBlock_of_length (length_masks i), count_masks]
  card_inter_le {i j} hij := by
    rw [← overlapCount_eq_card_inter (length_masks i) (length_masks j)]
    exact overlapCount_masks i j hij

/-- The positions of the block of a mask of length `ℓ`, in increasing order, are the positions
where the mask is `true`. -/
private theorem map_val_sort_maskBlock {w : List Bool} (hw : w.length = ℓ) :
    (maskBlock ℓ w).sort.map Fin.val = (List.range w.length).filter fun k => w.getD k false := by
  set l := (List.range w.length).filter fun k => w.getD k false
  have hset : (maskBlock ℓ w).map Fin.valEmbedding = l.toFinset := by
    ext k
    simp only [mem_map, mem_maskBlock, Fin.valEmbedding_apply, List.mem_toFinset, l,
      List.mem_filter, List.mem_range, hw]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.isLt, hk⟩
    · rintro ⟨hk, hw⟩
      exact ⟨⟨k, hk⟩, hw, rfl⟩
  have h := StrictMonoOn.map_finsetSort Fin.valEmbedding (maskBlock ℓ w) fun _ _ _ _ h => h
  rw [hset] at h
  exact h.trans ((List.toFinset_sort _ (List.nodup_range.filter _)).2
    ((List.pairwise_lt_range.filter _).imp le_of_lt))

/-- **Reading a block given by a mask.** The bits of a seed `z` in the block of a design given by
masks are the bits of `z` at the ones of the mask, in increasing order of position. -/
theorem ofFn_restrict_ofMasks (masks : Fin m → List Bool)
    (length_masks : ∀ i, (masks i).length = ℓ) (count_masks : ∀ i, (masks i).count true = n)
    (overlapCount_masks : ∀ i j, i ≠ j → overlapCount (masks i) (masks j) ≤ a) (i : Fin m)
    (z : Fin ℓ → Bool) :
    List.ofFn ((Design.ofMasks masks length_masks count_masks overlapCount_masks).restrict i z) =
      restrictMask (masks i) (List.ofFn z) := by
  set D := Design.ofMasks masks length_masks count_masks overlapCount_masks
  calc List.ofFn (D.restrict i z)
      = ((List.finRange n).map ((D.block i).orderEmbOfFin (D.card_block i))).map z := by
        rw [List.map_map, ← List.ofFn_eq_map]
        rfl
    _ = ((maskBlock ℓ (masks i)).sort.map Fin.val).map fun k => (List.ofFn z).getD k false := by
        rw [listMap_orderEmbOfFin_finRange, List.map_map]
        exact List.map_congr_left fun k _ => (List.getD_ofFn z k false).symm
    _ = restrictMask (masks i) (List.ofFn z) := by
        rw [map_val_sort_maskBlock (length_masks i), restrictMask]

/-! ### The greedy design -/

/-- One step of the greedy construction of a design: keep the candidate mask `w` when it has `n`
ones and shares at most `a` of them with every mask kept so far. -/
def greedyStep (n a : ℕ) (kept : List (List Bool)) (w : List Bool) : List (List Bool) :=
  if w.count true = n ∧ ∀ v ∈ kept, overlapCount w v ≤ a then kept ++ [w] else kept

/-- The greedy design [Arora and Barak, Chapter 20][AroraBarak09], as masks: the masks of length
`ℓ`, in the order of `Cslib.BitString.enumList`, each kept when it has `n` ones and shares at most
`a` of them with every mask kept before it. -/
def greedyMasks (ℓ n a : ℕ) : List (List Bool) :=
  (BitString.enumList ℓ).foldl (greedyStep n a) []

private theorem prefix_foldl_greedyStep (cands kept : List (List Bool)) :
    kept <+: cands.foldl (greedyStep n a) kept := by
  induction cands generalizing kept with
  | nil => exact List.prefix_refl _
  | cons w cands ih =>
    refine List.IsPrefix.trans ?_ (ih _)
    unfold greedyStep
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

private theorem mem_foldl_greedyStep {cands kept : List (List Bool)} {v : List Bool}
    (hv : v ∈ cands.foldl (greedyStep n a) kept) : v ∈ kept ∨ v ∈ cands ∧ v.count true = n := by
  induction cands generalizing kept with
  | nil => exact .inl hv
  | cons w cands ih =>
    rcases ih hv with hv | ⟨hv, hn⟩
    · unfold greedyStep at hv
      split at hv
      · rename_i h
        rcases List.mem_append.1 hv with hv | hv
        · exact .inl hv
        · rw [List.mem_singleton.1 hv]
          exact .inr ⟨List.mem_cons_self .., h.1⟩
      · exact .inl hv
    · exact .inr ⟨List.mem_cons_of_mem _ hv, hn⟩

private theorem pairwise_foldl_greedyStep {cands kept : List (List Bool)}
    (h : kept.Pairwise fun u v => overlapCount v u ≤ a) :
    (cands.foldl (greedyStep n a) kept).Pairwise fun u v => overlapCount v u ≤ a := by
  induction cands generalizing kept with
  | nil => exact h
  | cons w cands ih =>
    refine ih ?_
    unfold greedyStep
    split
    · rename_i hw
      exact List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _,
        fun u hu v hv => List.mem_singleton.1 hv ▸ hw.2 u hu⟩
    · exact h

private theorem maximal_foldl_greedyStep {cands kept : List (List Bool)} {w : List Bool}
    (hw : w ∈ cands) (hn : w.count true = n) :
    w ∈ cands.foldl (greedyStep n a) kept ∨
      ∃ v ∈ cands.foldl (greedyStep n a) kept, a < overlapCount w v := by
  induction cands generalizing kept with
  | nil => exact absurd hw List.not_mem_nil
  | cons w' cands ih =>
    rcases List.mem_cons.1 hw with rfl | hw
    · rw [List.foldl_cons]
      have hpre := prefix_foldl_greedyStep (n := n) (a := a) cands (greedyStep n a kept w)
      by_cases h : w.count true = n ∧ ∀ v ∈ kept, overlapCount w v ≤ a
      · have hstep : greedyStep n a kept w = kept ++ [w] := ite_eq_left h
        rw [hstep] at hpre ⊢
        exact .inl (hpre.subset (List.mem_append_right _ (List.mem_singleton_self _)))
      · have hstep : greedyStep n a kept w = kept := ite_eq_right h
        rw [hstep] at hpre ⊢
        push Not at h
        obtain ⟨v, hv, hlt⟩ := h hn
        exact .inr ⟨v, hpre.subset hv, hlt⟩
    · exact ih hw

variable {w : List Bool}

/-- Every mask of the greedy design has length `ℓ`. -/
theorem length_of_mem_greedyMasks (hw : w ∈ greedyMasks ℓ n a) : w.length = ℓ := by
  rcases mem_foldl_greedyStep hw with hw | ⟨hw, -⟩
  · exact absurd hw List.not_mem_nil
  · exact BitString.mem_enumList.1 hw

/-- Every mask of the greedy design has `n` ones. -/
theorem count_of_mem_greedyMasks (hw : w ∈ greedyMasks ℓ n a) : w.count true = n := by
  rcases mem_foldl_greedyStep hw with hw | ⟨-, hn⟩
  · exact absurd hw List.not_mem_nil
  · exact hn

/-- Each mask of the greedy design shares at most `a` ones with every earlier one. -/
theorem pairwise_greedyMasks :
    (greedyMasks ℓ n a).Pairwise fun u v => overlapCount v u ≤ a :=
  pairwise_foldl_greedyStep List.Pairwise.nil

/-- **The greedy design is maximal.** If `a < n`, every mask of length `ℓ` with `n` ones shares
more than `a` ones with some mask of the greedy design. -/
theorem exists_mem_greedyMasks_lt_overlapCount (han : a < n) (hw : w.length = ℓ)
    (hn : w.count true = n) : ∃ v ∈ greedyMasks ℓ n a, a < overlapCount w v := by
  rcases maximal_foldl_greedyStep (BitString.mem_enumList.2 hw) hn with hmem | h
  · exact ⟨w, hmem, by rwa [overlapCount_self, hn]⟩
  · exact h

/-- At most `C(ℓ - t, n - t)` sets of `n` elements of `Fin ℓ` contain a given set of `t`
elements. -/
private theorem card_filter_superset_le {T : Finset (Fin ℓ)} {t : ℕ} (hT : #T = t) :
    #{S ∈ powersetCard n univ | T ⊆ S} ≤ (ℓ - t).choose (n - t) := by
  calc #{S ∈ powersetCard n univ | T ⊆ S}
      ≤ #(powersetCard (n - t) (univ \ T)) := by
        refine card_le_card_of_injOn (· \ T) (fun S hS => ?_) (fun S hS S' hS' h => ?_)
        · rw [mem_coe, mem_filter, mem_powersetCard] at hS
          rw [mem_coe, mem_powersetCard]
          refine ⟨sdiff_subset_sdiff (subset_univ _) subset_rfl, ?_⟩
          rw [card_sdiff, inter_eq_left.2 hS.2, hS.1.2, hT]
        · rw [mem_coe, mem_filter] at hS hS'
          rw [← sdiff_union_of_subset hS.2, ← sdiff_union_of_subset hS'.2]
          exact congrArg (· ∪ T) h
    _ = (ℓ - t).choose (n - t) := by
        rw [card_powersetCard, card_sdiff, inter_univ, card_univ, Fintype.card_fin, hT]

/-- At most `C(n, t) C(ℓ - t, n - t)` sets of `n` elements of `Fin ℓ` share at least `t` elements
with a given set of `n` elements. -/
private theorem card_filter_le_card_inter_le {B : Finset (Fin ℓ)} (hB : #B = n) (t : ℕ) :
    #{S ∈ powersetCard n univ | t ≤ #(S ∩ B)} ≤ n.choose t * (ℓ - t).choose (n - t) := by
  calc #{S ∈ powersetCard n univ | t ≤ #(S ∩ B)}
      ≤ #((powersetCard t B).biUnion fun T => {S ∈ powersetCard n univ | T ⊆ S}) := by
        refine card_le_card fun S hS => ?_
        obtain ⟨hS, ht⟩ := mem_filter.1 hS
        obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq ht
        exact mem_biUnion.2 ⟨T, mem_powersetCard.2 ⟨hTS.trans inter_subset_right, hT⟩,
          mem_filter.2 ⟨hS, hTS.trans inter_subset_left⟩⟩
    _ ≤ ∑ T ∈ powersetCard t B, #{S ∈ powersetCard n univ | T ⊆ S} := card_biUnion_le
    _ ≤ ∑ _T ∈ powersetCard t B, (ℓ - t).choose (n - t) :=
        sum_le_sum fun T hT => card_filter_superset_le (mem_powersetCard.1 hT).2
    _ = n.choose t * (ℓ - t).choose (n - t) := by
        rw [sum_const, card_powersetCard, hB, smul_eq_mul]

/-- **The greedy design is large.** If `a < n ≤ ℓ`, the greedy design has at least
`C(ℓ, a + 1) / C(n, a + 1) ^ 2` masks: by maximality every set of `n` elements of `Fin ℓ` shares
`a + 1` elements with some block, and a block shares `a + 1` elements with at most
`C(n, a + 1) C(ℓ - a - 1, n - a - 1)` of them. -/
theorem choose_le_length_greedyMasks_mul (han : a < n) (hnℓ : n ≤ ℓ) :
    ℓ.choose (a + 1) ≤ (greedyMasks ℓ n a).length * n.choose (a + 1) ^ 2 := by
  set F := greedyMasks ℓ n a
  set K := (ℓ - (a + 1)).choose (n - (a + 1))
  -- every `n`-set shares `a + 1` elements with a block of `F`
  have hcover : powersetCard n (univ : Finset (Fin ℓ)) ⊆
      F.toFinset.biUnion fun v => {S ∈ powersetCard n univ | a + 1 ≤ #(S ∩ maskBlock ℓ v)} := by
    intro S hS
    set w := List.ofFn fun k : Fin ℓ => decide (k ∈ S)
    have hlen : w.length = ℓ := List.length_ofFn
    have hblock : maskBlock ℓ w = S := by
      ext k
      simp [w, List.getD_eq_getElem?_getD]
    have hcount : w.count true = n := by
      rw [count_true_eq_card_maskBlock_of_length hlen, hblock, (mem_powersetCard.1 hS).2]
    obtain ⟨v, hv, hlt⟩ := exists_mem_greedyMasks_lt_overlapCount han hlen hcount
    rw [overlapCount_eq_card_inter hlen (length_of_mem_greedyMasks hv), hblock] at hlt
    exact mem_biUnion.2 ⟨v, List.mem_toFinset.2 hv, mem_filter.2 ⟨hS, hlt⟩⟩
  have hcount : ℓ.choose n ≤ F.length * (n.choose (a + 1) * K) := by
    calc ℓ.choose n = #(powersetCard n (univ : Finset (Fin ℓ))) := by
          rw [card_powersetCard, card_univ, Fintype.card_fin]
      _ ≤ ∑ v ∈ F.toFinset, #{S ∈ powersetCard n univ | a + 1 ≤ #(S ∩ maskBlock ℓ v)} :=
          (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _v ∈ F.toFinset, n.choose (a + 1) * K := by
          refine sum_le_sum fun v hv => card_filter_le_card_inter_le ?_ (a + 1)
          have hv := List.mem_toFinset.1 hv
          rw [← count_true_eq_card_maskBlock_of_length (length_of_mem_greedyMasks hv),
            count_of_mem_greedyMasks hv]
      _ ≤ F.length * (n.choose (a + 1) * K) := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (List.toFinset_card_le F)
  have hK : 0 < K := Nat.choose_pos (Nat.sub_le_sub_right hnℓ _)
  refine Nat.le_of_mul_le_mul_right ?_ hK
  calc ℓ.choose (a + 1) * K = ℓ.choose n * n.choose (a + 1) := (Nat.choose_mul han).symm
    _ ≤ F.length * (n.choose (a + 1) * K) * n.choose (a + 1) := Nat.mul_le_mul_right _ hcount
    _ = F.length * n.choose (a + 1) ^ 2 * K := by ring

/-- `b ^ t ≤ C((b + 1) t, t)`. -/
private theorem pow_le_choose_succ_mul (b t : ℕ) : b ^ t ≤ ((b + 1) * t).choose t := by
  have h₁ : (b * t) ^ t ≤ ((b + 1) * t).descFactorial t :=
    (Nat.pow_le_pow_left (by rw [Nat.add_mul, one_mul]; omega) t).trans
      (Nat.pow_sub_le_descFactorial _ t)
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_pow] at h₁
  have h₂ : b ^ t * t.factorial ≤ t.factorial * ((b + 1) * t).choose t :=
    (Nat.mul_le_mul_left _ (Nat.factorial_le_pow t)).trans h₁
  rw [mul_comm] at h₂
  exact Nat.le_of_mul_le_mul_left h₂ (Nat.factorial_pos t)

/-- **The greedy design with seeds of linear length.** If `0 < t ≤ n ≤ (b + 1) t` and
`4 ^ n m ≤ b ^ t`, the greedy design on seeds of `(b + 1) t` bits, with blocks of `n` positions
sharing at most `t - 1` of them, has at least `m` blocks. -/
theorem le_length_greedyMasks {b t : ℕ} (ht : 0 < t) (htn : t ≤ n) (hn : n ≤ (b + 1) * t)
    (hm : 4 ^ n * m ≤ b ^ t) : m ≤ (greedyMasks ((b + 1) * t) n (t - 1)).length := by
  have h := choose_le_length_greedyMasks_mul (ℓ := (b + 1) * t) (a := t - 1) (by omega) hn
  rw [Nat.sub_add_cancel ht] at h
  have hc : n.choose t ^ 2 ≤ 4 ^ n := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.choose_le_two_pow n t) 2
  refine Nat.le_of_mul_le_mul_left (c := 4 ^ n) ?_ (by positivity)
  calc 4 ^ n * m ≤ ((b + 1) * t).choose t := hm.trans (pow_le_choose_succ_mul b t)
    _ ≤ _ * n.choose t ^ 2 := h
    _ ≤ _ * 4 ^ n := Nat.mul_le_mul_left _ hc
    _ = 4 ^ n * _ := mul_comm _ _

/-- The first `m` masks of the greedy design, as a design, when there are at least `m`. -/
def Design.greedy (ℓ n a m : ℕ) (h : m ≤ (greedyMasks ℓ n a).length) : Design ℓ n a m :=
  .ofMasks (fun i => (greedyMasks ℓ n a)[i])
    (fun i => length_of_mem_greedyMasks (List.getElem_mem _))
    (fun i => count_of_mem_greedyMasks (List.getElem_mem _))
    fun i j hij => by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · rw [overlapCount_comm]
        exact List.pairwise_iff_getElem.1 pairwise_greedyMasks i j _ _ hlt
      · exact List.pairwise_iff_getElem.1 pairwise_greedyMasks j i _ _ hlt

/-- Reading block `i` of the greedy design is `restrictMask` with the `i`-th greedy mask. -/
theorem ofFn_restrict_greedy (h : m ≤ (greedyMasks ℓ n a).length) (i : Fin m)
    (z : Fin ℓ → Bool) :
    List.ofFn ((Design.greedy ℓ n a m h).restrict i z) =
      restrictMask (greedyMasks ℓ n a)[i] (List.ofFn z) :=
  ofFn_restrict_ofMasks _ _ _ _ i z

/-- The Nisan–Wigderson generator on lists: for each mask `w` of `masks`, the value of `g` on the
first `n` bits of the seed `z` at the ones of `w`. -/
def listGenerator (g : List Bool → Bool) (n : ℕ) (masks : List (List Bool)) (z : List Bool) :
    List Bool :=
  masks.map fun w => g ((restrictMask w z).take n)

/-- With the first `m` masks of the greedy design, the generator on lists is the Nisan–Wigderson
generator of `Design.greedy` and of the function `g` on words of `n` bits. -/
theorem listGenerator_take_greedyMasks (h : m ≤ (greedyMasks ℓ n a).length)
    (g : List Bool → Bool) (z : Fin ℓ → Bool) :
    listGenerator g n ((greedyMasks ℓ n a).take m) (List.ofFn z) =
      List.ofFn (generator (Design.greedy ℓ n a m h) (fun x => g (List.ofFn x)) z) := by
  refine List.ext_getElem (by simp [listGenerator, h]) fun i hi hi' => ?_
  rw [List.length_ofFn] at hi'
  simp only [listGenerator, List.getElem_map, List.getElem_take, List.getElem_ofFn,
    generator_apply]
  have hrestrict := ofFn_restrict_greedy h ⟨i, hi'⟩ z
  have hlen : (restrictMask (greedyMasks ℓ n a)[i] (List.ofFn z)).length ≤ n :=
    (congrArg List.length hrestrict).symm.trans_le (List.length_ofFn).le
  rw [List.take_of_length_le hlen, hrestrict]
  rfl

/-! ### Fooling small circuits, in counting form -/

/-- The fraction of inputs where a negated test is `true`. -/
private theorem card_not_div {X : Type*} [Fintype X] [Nonempty X] (p : X → Bool) :
    (#{x | (!p x) = true} : ℝ) / Fintype.card X =
      1 - (#{x | p x = true} : ℝ) / Fintype.card X := by
  have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsum : #{x | p x = true} + #{x | (!p x) = true} = Fintype.card X := by
    rw [← card_univ, ← card_filter_add_card_filter_not (s := univ) (fun x => p x = true)]
    simp
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast (add_comm _ _).trans hsum

/-- **The Nisan–Wigderson generator fools small circuits, in counting form**
[NisanWigderson1994]. Let `f` be average-case hard for size `s` (with the non-strict bound of
`Cslib.Circuits.Boolean.IsAverageCaseHard`), let `S + 1 + m (2 ^ a (2 a + 3) + 1) + 1 ≤ s`, and
let `m < ε s`. Then for every test of De Morgan circuit complexity at most `S`, the fraction of
the `2 ^ ℓ` seeds on which the test accepts the output of the generator differs from the fraction
of the `2 ^ m` strings it accepts by less than `ε`. The slack `m < ε s` makes the agreement bound
`1 / 2 + 1 / s` strictly smaller than the `1 / 2 + ε / m` of the reconstruction. -/
theorem abs_card_div_sub_card_div_lt (D : Design ℓ n a m) {f : BooleanFunction n} {s S : ℕ}
    {ε : ℝ} (hf : IsAverageCaseHard f s) (hs : S + 1 + m * (2 ^ a * (2 * a + 3) + 1) + 1 ≤ s)
    (hm : (m : ℝ) < ε * s) (test : BooleanFunction m)
    (htest : complexity interpretation (single test) ≤ S) :
    |(#{z | test (generator D f z) = true} : ℝ) / 2 ^ ℓ - #{r | test r = true} / 2 ^ m| < ε := by
  have hcardSeed : (Fintype.card (Fin ℓ → Bool) : ℝ) = 2 ^ ℓ := by simp
  have hcardOut : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by simp
  have hεs : 0 < ε * s := lt_of_le_of_lt (Nat.cast_nonneg m) hm
  have hs0 : (0 : ℝ) < s := by
    rcases (Nat.cast_nonneg s : (0 : ℝ) ≤ s).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hεs
      exact absurd hεs (lt_irrefl 0)
  have hε : 0 < ε := pos_of_mul_pos_left hεs hs0.le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- with no output bits, the test sees the same empty string on every seed
    have hr (r : Fin 0 → Bool) : test r = test Fin.elim0 := congrArg test (Subsingleton.elim _ _)
    have hpow : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
    rcases hb : test Fin.elim0 with _ | _
    · rw [filter_false_of_mem fun z _ => by rw [hr, hb]; decide,
        filter_false_of_mem fun r _ => by rw [hr, hb]; decide]
      simpa using hε
    · rw [filter_true_of_mem fun z _ => by rw [hr, hb],
        filter_true_of_mem fun r _ => by rw [hr, hb]]
      simp [hpow, hε]
  -- the strict agreement bound of the reconstruction, from the slack
  have hslack : 1 / (s : ℝ) < ε / m := by
    rw [div_lt_div_iff₀ hs0 (by exact_mod_cast hm0)]
    linarith
  have hhard (S' : ℕ) (hS' : S' ≤ S + 1) (g : BooleanFunction n)
      (hg : complexity interpretation (single g) ≤ S' + m * (2 ^ a * (2 * a + 3) + 1) + 1) :
      (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + ε / m :=
    hf.div_lt hslack (hg.trans (by omega))
  have h₁ := toReal_realExperiment_sub_toReal_idealExperiment_lt D f hm0 (hhard S (by omega))
    test htest
  have h₂ := toReal_realExperiment_sub_toReal_idealExperiment_lt D f hm0 (hhard (S + 1) le_rfl)
    (fun r => !test r) ((complexity_not_le test).trans (by omega))
  rw [Generator.toReal_realExperiment_pure, Generator.toReal_idealExperiment_pure,
    nnratCast_dens, nnratCast_dens] at h₁ h₂
  rw [card_not_div (fun z => test (generator D f z)), card_not_div test] at h₂
  rw [hcardSeed, hcardOut] at h₁ h₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith

end Cslib.Crypto.PRG.NisanWigderson
