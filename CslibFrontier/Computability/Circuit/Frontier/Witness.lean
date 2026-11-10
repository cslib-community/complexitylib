/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Rectangle
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Data.BitString.Agree
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Dense rectangle-free sets and sets of small bias exist

The frontier lower bounds are stated for families of sets `S_n ⊆ U^n` that are rectangle-free,
or of small bias on large rectangles, with thresholds `K_n` such that `log K_n = o(n)`. This file
shows, by counting, that such families exist over the binary alphabet, so that the hypotheses of
the bundled claims `CircuitLowerBound` and `AverageCaseBound` are satisfiable.

**Dense rectangle-free sets** (`exists_rectangleFree_two_pow_le_ncard`). For `n` coordinates, some
set of at least `2 ^ (n - 1)` bit strings, half of the cube, is `(n + 2)`-rectangle-free. A set
containing a rectangle with both sides of size at least `K` contains one with sides of size
exactly `K`, and such a rectangle is spanned by `K` inputs `z i`: its sides are the parts of the
`z i` on the cut and off it. So there are at most `2 ^ n · (2 ^ n) ^ K` of them, each with `K ^ 2`
points, and at most `2 ^ (n + n K - K ^ 2)` of the `2 ^ (2 ^ n)` sets of bit strings contain one.
For `K = n + 2` this is a `2 ^ (-n - 4)` fraction, while at least half of all sets have at least
`2 ^ (n - 1)` elements.

**Sets of small bias** (`exists_rectangleBias`). If `n + 1 ≤ b ^ 2 K`, some set of bit strings
has density within `b` of `1/2` on every rectangle with both sides of size at least `K`. A
rectangle with sides of sizes `k₁` and `k₂` is spanned by `k₁ + k₂` inputs, and by Hoeffding's
inequality (`Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`) at most a
`2 exp (-2 b ^ 2 k₁ k₂)` fraction of all sets has bias more than `b` on it. The union bound over
all sizes and all spanning inputs is less than one.

For families over `Fin n`, the first gives the hypotheses of the worst-case claims with
`K_n = n + 2` (`exists_rectangleFree_family`), and the second those of the average-case claims with
`K_n = (n + 1) ^ 3` and bias `b_n = 1 / (n + 1) → 0` (`exists_rectangleBias_family`).

## Main results

* `Cslib.Circuits.Frontier.exists_rectangleFree_two_pow_le_ncard`: dense rectangle-free sets.
* `Cslib.Circuits.Frontier.exists_rectangleFree_family`: a family meeting the hypotheses of the
  worst-case frontier lower bounds.
* `Cslib.Circuits.Frontier.exists_rectangleBias`: sets of small bias on large rectangles.
* `Cslib.Circuits.Frontier.exists_rectangleBias_family`: a family meeting the hypotheses of the
  average-case frontier lower bounds, with bias tending to zero.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [E. Kushilevitz, N. Nisan, *Communication Complexity*, Ch. 1][KushilevitzNisan1997]
-/

public section

namespace Cslib.Circuits.Frontier

open Set Finset Filter Asymptotics Real

variable {ι U : Type*}

/-! ### Rectangles spanned by inputs -/

/-- A set with `k` elements, counted with `encard`, is the range of an injective map from
`Fin k`. -/
private theorem exists_injective_range_eq {α : Type*} {s : Set α} {k : ℕ} (hs : s.encard = k) :
    ∃ a : Fin k → α, Function.Injective a ∧ range a = s := by
  have hfin := Set.finite_of_encard_eq_coe hs
  have : Finite s := hfin.to_subtype
  have hcard : Nat.card (Fin k) = Nat.card s := by
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact_mod_cast (hfin.cast_ncard_eq.trans hs).symm
  obtain ⟨e⟩ := Finite.card_eq.mp hcard
  exact ⟨fun i => (e i : α), Subtype.val_injective.comp e.injective, by
    rw [show (fun i => (e i : α)) = Subtype.val ∘ e from rfl, e.surjective.range_comp,
      Subtype.range_coe]⟩

/-- An input with a given part on `X` and a given part off `X`. -/
private theorem exists_domRestrict_eq (X : Set ι) (u : X → U) (v : ↥Xᶜ → U) :
    ∃ x : ι → U, X.domRestrict x = u ∧ Xᶜ.domRestrict x = v := by
  classical
  obtain ⟨x, hx⟩ := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).surjective (u, v)
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

/-- A rectangle inside a set with both sides of size at least `K` gives `K` inputs `z i` spanning
a rectangle inside it with `K ^ 2` points: the parts of the `z i` on `X` and off `X` are the
sides. -/
private theorem exists_rectangle_range_subset {X : Set ι} {A : Set (X → U)} {B : Set (↥Xᶜ → U)}
    {K : ℕ} (hA : K ≤ A.encard) (hB : K ≤ B.encard) :
    ∃ z : Fin K → ι → U,
      rectangle X (range fun i => X.domRestrict (z i)) (range fun j => Xᶜ.domRestrict (z j)) ⊆
        rectangle X A B ∧
      (rectangle X (range fun i => X.domRestrict (z i))
        (range fun j => Xᶜ.domRestrict (z j))).ncard = K * K := by
  obtain ⟨A', hA'A, hA'⟩ := exists_subset_encard_eq hA
  obtain ⟨B', hB'B, hB'⟩ := exists_subset_encard_eq hB
  obtain ⟨a, ha, rfl⟩ := exists_injective_range_eq hA'
  obtain ⟨b, hb, rfl⟩ := exists_injective_range_eq hB'
  choose z hz using fun i => exists_domRestrict_eq X (a i) (b i)
  have hza : (fun i => X.domRestrict (z i)) = a := funext fun i => (hz i).1
  have hzb : (fun j => Xᶜ.domRestrict (z j)) = b := funext fun j => (hz j).2
  refine ⟨z, ?_, ?_⟩
  · rw [hza, hzb]
    exact fun x hx => ⟨hA'A hx.1, hB'B hx.2⟩
  · rw [hza, hzb, ncard_rectangle, ncard_range_of_injective ha, ncard_range_of_injective hb,
      Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Every rectangle with finite sides is spanned by inputs, one for each element of each side:
its sides are the parts on `X` of the inputs `x i` and the parts off `X` of the inputs `y j`. -/
private theorem exists_eq_rectangle_range [Nonempty U] {X : Set ι} {A : Set (X → U)}
    {B : Set (↥Xᶜ → U)} (hA : A.Finite) (hB : B.Finite) :
    ∃ (x : Fin A.ncard → ι → U) (y : Fin B.ncard → ι → U),
      rectangle X (range fun i => X.domRestrict (x i)) (range fun j => Xᶜ.domRestrict (y j)) =
        rectangle X A B := by
  obtain ⟨a, -, ha⟩ := exists_injective_range_eq hA.cast_ncard_eq.symm
  obtain ⟨b, -, hb⟩ := exists_injective_range_eq hB.cast_ncard_eq.symm
  choose x hx using fun i => exists_domRestrict_eq X (a i) fun _ => Classical.arbitrary U
  choose y hy using fun j => exists_domRestrict_eq X (fun _ => Classical.arbitrary U) (b j)
  refine ⟨x, y, ?_⟩
  rw [show (fun i => X.domRestrict (x i)) = a from funext fun i => (hx i).1,
    show (fun j => Xᶜ.domRestrict (y j)) = b from funext fun j => (hy j).2, ha, hb]

/-! ### Dense rectangle-free sets -/

section RectangleFree

variable [Fintype ι]

/-- At least half of the sets of bit strings have at least `2 ^ (n - 1)` elements: complementing
a smaller set gives a larger one. -/
private theorem two_pow_le_two_mul_card_filter [DecidableEq ι] :
    2 ^ Fintype.card (ι → Bool) ≤
      2 * #{f : (ι → Bool) → Bool | 2 ^ (Fintype.card ι - 1) ≤ #{x | f x = true}} := by
  classical
  set t := 2 ^ (Fintype.card ι - 1)
  have hN : 2 * t ≤ Fintype.card (ι → Bool) + 1 := by
    simp only [t, Fintype.card_fun, Fintype.card_bool]
    rcases Fintype.card ι with _ | n
    · norm_num
    · rw [Nat.add_sub_cancel, pow_succ]
      omega
  -- Complementing is an injection from the small sets into the large ones.
  have hsmall : #{f : (ι → Bool) → Bool | ¬ t ≤ #{x | f x = true}} ≤
      #{f : (ι → Bool) → Bool | t ≤ #{x | f x = true}} := by
    refine card_le_card_of_injOn (fun f x => !f x) (fun f hf => ?_)
      fun f _ g _ h => funext fun x => by simpa using congrFun h x
    have hf : #{x | f x = true} < t := by simpa using hf
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (ι → Bool)))
      fun x => f x = true
    simp only [card_univ, Bool.not_eq_true] at hsplit
    have hneg : #{x | (!f x) = true} = #{x | f x = false} := by
      simp only [Bool.not_eq_true']
    simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hneg]
    omega
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset ((ι → Bool) → Bool)))
    fun f => t ≤ #{x | f x = true}
  rw [card_univ, Fintype.card_fun, Fintype.card_bool] at hsplit
  omega

/-- **Dense rectangle-free sets exist.** For `n` coordinates, some set of at least `2 ^ (n - 1)`
bit strings, half of the cube, is `(n + 2)`-rectangle-free.

At most `2 ^ (n + n K)` rectangles with sides of size exactly `K` are spanned by `K` inputs, each
with `K ^ 2` points; for `K = n + 2` at most a `2 ^ (-n - 4)` fraction of all sets of bit strings
contains one, while at least half of them have at least `2 ^ (n - 1)` elements. -/
theorem exists_rectangleFree_two_pow_le_ncard :
    ∃ S : Set (ι → Bool), RectangleFree S (Fintype.card ι + 2) ∧
      2 ^ (Fintype.card ι - 1) ≤ S.ncard := by
  classical
  set n := Fintype.card ι
  set K := n + 2
  set N := Fintype.card (ι → Bool)
  have hN : N = 2 ^ n := by simp [N, n]
  -- The rectangle spanned by `K` inputs, and the sets containing it with `K ^ 2` points.
  let R (w : Set ι × (Fin K → ι → Bool)) : Set (ι → Bool) :=
    rectangle w.1 (range fun i => w.1.domRestrict (w.2 i))
      (range fun j => w.1ᶜ.domRestrict (w.2 j))
  let E (w : Set ι × (Fin K → ι → Bool)) : Finset ((ι → Bool) → Bool) :=
    {f : (ι → Bool) → Bool | (R w).ncard = K * K ∧ ∀ x ∈ R w, f x = true}
  have hE (w : Set ι × (Fin K → ι → Bool)) : #(E w) * 2 ^ (K * K) ≤ 2 ^ N := by
    by_cases hw : (R w).ncard = K * K
    · have hEw : E w = ({f : (ι → Bool) → Bool |
          ∀ x ∉ (R w).toFinsetᶜ, f x = (fun _ => true) x} : Finset _) := by
        ext f
        simp [E, hw]
      have hle : K * K ≤ N := hw ▸ (ncard_le_card _).trans_eq Nat.card_eq_fintype_card
      rw [hEw, BitString.card_filter_forall_notMem_eq, card_compl, ← ncard_eq_toFinset_card', hw,
        ← pow_add, Nat.sub_add_cancel hle]
    · have hEw : E w = ∅ := by
        ext f
        simp [E, hw]
      simp [hEw]
  -- Every set that is not `K`-rectangle-free contains a spanned rectangle with `K ^ 2` points.
  set bad : Finset ((ι → Bool) → Bool) :=
    {f : (ι → Bool) → Bool | ¬ RectangleFree {x | f x = true} K}
  have hbad : bad ⊆ univ.biUnion E := by
    intro f hf
    simp only [bad, RectangleFree, mem_filter, Finset.mem_univ, true_and, not_forall, not_or,
      not_lt] at hf
    obtain ⟨X, A, B, hAB, hA, hB⟩ := hf
    obtain ⟨z, hz, hcard⟩ := exists_rectangle_range_subset hA hB
    exact mem_biUnion.mpr ⟨(X, z), Finset.mem_univ _,
      mem_filter.mpr ⟨Finset.mem_univ _, hcard, fun x hx => hAB (hz hx)⟩⟩
  have hcount : #bad * 2 ^ (n + 4) ≤ 2 ^ N := by
    have hW : Fintype.card (Set ι × (Fin K → ι → Bool)) = 2 ^ n * 2 ^ (n * K) := by
      simp [n, Fintype.card_set, ← pow_mul]
    have hsum : #bad * 2 ^ (K * K) ≤ 2 ^ n * 2 ^ (n * K) * 2 ^ N := by
      calc #bad * 2 ^ (K * K) ≤ (∑ w, #(E w)) * 2 ^ (K * K) :=
            Nat.mul_le_mul_right _ ((Finset.card_le_card hbad).trans card_biUnion_le)
        _ = ∑ w, #(E w) * 2 ^ (K * K) := sum_mul _ _ _
        _ ≤ ∑ _w : Set ι × (Fin K → ι → Bool), 2 ^ N := sum_le_sum fun w _ => hE w
        _ = 2 ^ n * 2 ^ (n * K) * 2 ^ N := by rw [sum_const, card_univ, hW, smul_eq_mul]
    have hKK : K * K = n + n * K + (n + 4) := by simp only [K]; ring
    rw [hKK, pow_add, pow_add] at hsum
    have hpos : 0 < 2 ^ n * 2 ^ (n * K) := by positivity
    nlinarith
  -- Some large set is rectangle-free.
  have hlarge := two_pow_le_two_mul_card_filter (ι := ι)
  have hlt : #bad < #{f : (ι → Bool) → Bool | 2 ^ (n - 1) ≤ #{x | f x = true}} := by
    have h16 : 16 ≤ 2 ^ (n + 4) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have hone : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    generalize 2 ^ N = P at hcount hlarge hone
    generalize 2 ^ (n + 4) = Q at hcount h16
    nlinarith
  obtain ⟨f, hf, hfbad⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨{x | f x = true}, ?_, ?_⟩
  · simpa [bad] using hfbad
  · have : ({x | f x = true} : Set (ι → Bool)) = ↑({x | f x = true} : Finset (ι → Bool)) := by
      ext
      simp
    rw [this, ncard_coe_finset]
    exact (mem_filter.mp hf).2

end RectangleFree

/-! ### Sets of small bias -/

section RectangleBias

/-- **Hoeffding's inequality for a random set of inputs.** For a fixed set `T`, the sets
`{x | f x = true}` whose density on `T` is more than `b` away from `1/2` are at most a
`2 exp (-2 b ^ 2 |T|)` fraction of all sets. -/
private theorem card_filter_lt_abs_le {α : Type*} [Fintype α] [DecidableEq α] (T : Set α) {b : ℝ}
    (hb : 0 ≤ b) :
    (#{f : α → Bool | b * T.ncard < |((T ∩ {x | f x = true}).ncard : ℝ) - T.ncard / 2|} : ℝ) ≤
      2 * 2 ^ Fintype.card α * exp (-(2 * b ^ 2 * T.ncard)) := by
  classical
  set R := T.toFinset
  have hT : T.ncard = #R := ncard_eq_toFinset_card' T
  have hTS (f : α → Bool) : (T ∩ {x | f x = true}).ncard = #{x ∈ R | f x = true} := by
    rw [ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [R]
  calc (#{f : α → Bool | b * T.ncard < |((T ∩ {x | f x = true}).ncard : ℝ) - T.ncard / 2|} : ℝ)
      ≤ #{f : α → Bool | b * #R ≤ |(#{x ∈ R | f x = true} : ℝ) - #R / 2|} := by
        refine Nat.cast_le.mpr (Finset.card_le_card fun f hf => ?_)
        simp only [mem_filter, Finset.mem_univ, true_and] at hf ⊢
        rw [← hTS, ← hT]
        exact hf.le
    _ ≤ 2 * 2 ^ Fintype.card α * exp (-(2 * (b * #R) ^ 2 / #R)) :=
        BitString.card_filter_le_abs_card_filter_sub_half_le R (by positivity)
    _ = 2 * 2 ^ Fintype.card α * exp (-(2 * b ^ 2 * T.ncard)) := by
        rw [hT]
        rcases eq_or_ne (#R : ℝ) 0 with h | h
        · simp [h]
        · congr 3
          field_simp

variable [Fintype ι]

/-- **Sets of small bias exist.** If `n + 1 ≤ b ^ 2 K` for `n = |ι|` and `b > 0`, some set of bit
strings has density within `b` of `1/2` on every rectangle with both sides of size at least `K`.

A rectangle with sides of sizes `k₁, k₂ ≥ K` is spanned by `k₁ + k₂` inputs, so there are at
most `2 ^ (n + n k₁ + n k₂)` of them, and by Hoeffding's inequality at most a
`2 exp (-2 b ^ 2 k₁ k₂) ≤ 2 exp (-(n + 1) (k₁ + k₂))` fraction of all sets of bit strings has bias
more than `b` on each. Summed over all sizes, this is less than one. -/
theorem exists_rectangleBias {K : ℕ} {b : ℝ} (hb : 0 < b)
    (hK : (Fintype.card ι + 1 : ℝ) ≤ b ^ 2 * K) : ∃ S : Set (ι → Bool), RectangleBias S K b := by
  classical
  -- Every set has bias at most `1/2`.
  rcases le_or_gt (1 / 2) b with hb2 | hb2
  · exact ⟨∅, fun X A B hA hB => (rectangleBias_one_half ∅ K X A B hA hB).trans
      (mul_le_mul_of_nonneg_right hb2 (Nat.cast_nonneg _))⟩
  set n := Fintype.card ι
  set N := Fintype.card (ι → Bool)
  have hN : N = 2 ^ n := by simp [N, n]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKpos : (0 : ℝ) < K := by
    rcases hK0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hK
      linarith
  have hK4 : 4 * ((n : ℝ) + 1) < K := by
    have hb2' : b ^ 2 < 1 / 4 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hb2' hKpos]
  have hK1 : 1 ≤ K := by exact_mod_cast hKpos
  -- The rectangle spanned by `k₁ + k₂` inputs, and the sets of large bias on it.
  let R (k₁ k₂ : ℕ) (w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool)) : Set (ι → Bool) :=
    rectangle w.1 (range fun i => w.1.domRestrict (w.2.1 i))
      (range fun j => w.1ᶜ.domRestrict (w.2.2 j))
  let E (k₁ k₂ : ℕ) (w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool)) :
      Finset ((ι → Bool) → Bool) :=
    {f : (ι → Bool) → Bool | (R k₁ k₂ w).ncard = k₁ * k₂ ∧
      b * (R k₁ k₂ w).ncard < |((R k₁ k₂ w ∩ {x | f x = true}).ncard : ℝ) - (R k₁ k₂ w).ncard / 2|}
  have hE (k₁ k₂ : ℕ) (w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool)) :
      (#(E k₁ k₂ w) : ℝ) ≤ 2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) := by
    by_cases hw : (R k₁ k₂ w).ncard = k₁ * k₂
    · rw [← hw]
      refine le_trans ?_ (card_filter_lt_abs_le (R k₁ k₂ w) hb.le)
      exact Nat.cast_le.mpr (Finset.card_le_card (monotone_filter_right _ fun f _ hf => hf.2))
    · have hEw : E k₁ k₂ w = ∅ := by
        ext f
        simp [E, hw]
      rw [hEw, Finset.card_empty, Nat.cast_zero]
      positivity
  -- Every set of large bias on some rectangle has large bias on a spanned rectangle.
  set bad : Finset ((ι → Bool) → Bool) :=
    {f : (ι → Bool) → Bool | ¬ RectangleBias {x | f x = true} K b}
  have hbad : bad ⊆ (Finset.Icc K N).biUnion fun k₁ => (Finset.Icc K N).biUnion fun k₂ =>
      Finset.univ.biUnion (E k₁ k₂) := by
    intro f hf
    simp only [bad, RectangleBias, mem_filter, Finset.mem_univ, true_and, not_forall,
      not_le] at hf
    obtain ⟨X, A, B, hA, hB, hbias⟩ := hf
    obtain ⟨x, y, hxy⟩ := exists_eq_rectangle_range (toFinite A) (toFinite B)
    have hR : (rectangle X A B).ncard = A.ncard * B.ncard := ncard_rectangle X A B
    have hRN : (rectangle X A B).ncard ≤ N := (ncard_le_card _).trans_eq Nat.card_eq_fintype_card
    have hAN : A.ncard ≤ N := (Nat.le_mul_of_pos_right _ (by omega)).trans (hR ▸ hRN)
    have hBN : B.ncard ≤ N := (Nat.le_mul_of_pos_left _ (by omega)).trans (hR ▸ hRN)
    refine mem_biUnion.mpr ⟨A.ncard, mem_Icc.mpr ⟨hA, hAN⟩, mem_biUnion.mpr ⟨B.ncard,
      mem_Icc.mpr ⟨hB, hBN⟩, mem_biUnion.mpr ⟨(X, x, y), Finset.mem_univ _, ?_⟩⟩⟩
    simp only [E, R, mem_filter, Finset.mem_univ, true_and]
    rw [hxy]
    exact ⟨hR, hbias⟩
  -- The union bound for rectangles with sides of sizes `k₁` and `k₂`.
  have hterm (k₁ k₂ : ℕ) (hk₁ : K ≤ k₁) (hk₂ : K ≤ k₂) :
      ∑ w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool), (#(E k₁ k₂ w) : ℝ) ≤
        2 ^ (n + 1) * 2 ^ N * exp (-(2 * K)) := by
    have hk₁' : (K : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    have hk₂' : (K : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    have hcard : (Fintype.card (Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool)) : ℝ) =
        2 ^ n * 2 ^ (n * k₁ + n * k₂) := by
      simp [n, Fintype.card_set, ← pow_mul, pow_add]
    have hexp : (2 : ℝ) ^ (n * k₁ + n * k₂) * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) ≤
        exp (-(2 * K)) := by
      refine (mul_le_mul_of_nonneg_right (two_pow_le_exp _) (exp_pos _).le).trans ?_
      rw [← exp_add, exp_le_exp]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hk₁' (by positivity : (0 : ℝ) ≤ b ^ 2 * k₂),
        mul_le_mul_of_nonneg_left hk₂' (by positivity : (0 : ℝ) ≤ b ^ 2 * k₁),
        mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ k₁),
        mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ k₂)]
    calc ∑ w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool), (#(E k₁ k₂ w) : ℝ)
        ≤ ∑ _w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool),
            2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) := sum_le_sum fun w _ => hE k₁ k₂ w
      _ = 2 ^ (n + 1) * 2 ^ N *
            ((2 : ℝ) ^ (n * k₁ + n * k₂) * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ)))) := by
          rw [sum_const, card_univ, nsmul_eq_mul, hcard]
          ring
      _ ≤ 2 ^ (n + 1) * 2 ^ N * exp (-(2 * K)) := by gcongr
  -- Summed over all sizes, fewer than all sets have large bias.
  have hcount : (#bad : ℝ) < 2 ^ N := by
    have hIcc : #(Finset.Icc K N) ≤ N := by
      rw [Nat.card_Icc]
      omega
    calc (#bad : ℝ)
        ≤ ∑ k₁ ∈ Finset.Icc K N, ∑ k₂ ∈ Finset.Icc K N,
            ∑ w : Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool), (#(E k₁ k₂ w) : ℝ) := by
          refine le_trans (Nat.cast_le.mpr ((Finset.card_le_card hbad).trans (card_biUnion_le.trans
            (sum_le_sum fun k₁ _ => card_biUnion_le.trans
              (sum_le_sum fun k₂ _ => card_biUnion_le))))) ?_
          push_cast
          rfl
      _ ≤ ∑ _k₁ ∈ Finset.Icc K N, ∑ _k₂ ∈ Finset.Icc K N, 2 ^ (n + 1) * 2 ^ N * exp (-(2 * K)) :=
          sum_le_sum fun k₁ hk₁ => sum_le_sum fun k₂ hk₂ =>
            hterm k₁ k₂ (mem_Icc.mp hk₁).1 (mem_Icc.mp hk₂).1
      _ ≤ N * N * (2 ^ (n + 1) * 2 ^ N * exp (-(2 * K))) := by
          simp only [sum_const, nsmul_eq_mul, ← mul_assoc]
          have : (#(Finset.Icc K N) : ℝ) ≤ N := by exact_mod_cast hIcc
          gcongr
      _ = (2 : ℝ) ^ (3 * n + 1) * exp (-(2 * K)) * 2 ^ N := by
          rw [hN]
          push_cast
          ring
      _ < 2 ^ N := by
          refine mul_lt_of_lt_one_left (by positivity) ?_
          refine (mul_le_mul_of_nonneg_right (two_pow_le_exp _) (exp_pos _).le).trans_lt ?_
          rw [← exp_add, exp_lt_one_iff]
          push_cast
          linarith
  by_contra! h
  have huniv : bad = Finset.univ := eq_univ_of_forall fun f => by simp [bad, h]
  rw [huniv, card_univ, Fintype.card_fun, Fintype.card_bool] at hcount
  push_cast at hcount
  exact lt_irrefl _ hcount

end RectangleBias

/-! ### Families meeting the hypotheses of the frontier lower bounds -/

/-- `log (n + c) = o(n)`. -/
private theorem isLittleO_log_add (c : ℝ) :
    (fun n : ℕ => Real.log ((n : ℝ) + c)) =o[atTop] fun n => (n : ℝ) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  exact (isLittleO_log_id_atTop.comp_tendsto h).trans_isBigO
    ((isBigO_refl _ _).add (isLittleO_const_id_atTop c).natCast_atTop.isBigO)

/-- **The hypotheses of the worst-case frontier lower bounds can be met.** There is a family of
sets `S_n ⊆ Bool^n` that are `(n + 2)`-rectangle-free, with `log (n + 2) = o(n)` and
`n log 2 - log |S_n| = o(n)`: the three fields of `DenseRectangleFree`, the hypothesis of
`CircuitLowerBound`, for the alphabet `Bool` and `K_n = n + 2`. Moreover `|S_n| ≥ 2 ^ (n - 1)`. -/
theorem exists_rectangleFree_family :
    ∃ S : ∀ n, Set (Fin n → Bool), (∀ᶠ n in atTop, RectangleFree (S n) (n + 2)) ∧
      (fun n : ℕ => Real.log ((n + 2 : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      (fun n => n * Real.log (Nat.card Bool) - Real.log (S n).ncard) =o[atTop]
        (fun n => (n : ℝ)) ∧ ∀ n, 2 ^ (n - 1) ≤ (S n).ncard := by
  choose S hfree hdense using fun n : ℕ => exists_rectangleFree_two_pow_le_ncard (ι := Fin n)
  simp only [Fintype.card_fin] at hfree hdense
  refine ⟨S, Eventually.of_forall hfree, ?_, ?_, hdense⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using isLittleO_log_add 2
  -- `n log 2 - log |S_n|` lies between `0` and `log 2`.
  refine (IsBigO.of_bound (Real.log 2) (Eventually.of_forall fun n => ?_)).trans_isLittleO
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hlow : (2 : ℝ) ^ (n - 1) ≤ (S n).ncard := by exact_mod_cast hdense n
  have hup : ((S n).ncard : ℝ) ≤ 2 ^ n := by
    have := ncard_le_card (S n)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] at this
    exact_mod_cast this
  have hlog_low : ((n : ℝ) - 1) * Real.log 2 ≤ Real.log (S n).ncard := by
    calc ((n : ℝ) - 1) * Real.log 2 ≤ ((n - 1 : ℕ) : ℝ) * Real.log 2 := by
          gcongr
          rcases n with _ | n <;> simp
      _ = Real.log (2 ^ (n - 1)) := by rw [Real.log_pow]
      _ ≤ Real.log (S n).ncard := Real.log_le_log hpos hlow
  have hlog_up : Real.log (S n).ncard ≤ n * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (hpos.trans_le hlow) hup
  rw [Nat.card_eq_fintype_card, Fintype.card_bool, Nat.cast_ofNat, Real.norm_eq_abs, norm_one,
    mul_one, abs_le]
  constructor <;> linarith

/-- **The hypotheses of the average-case frontier lower bounds can be met with bias tending to
zero.** There is a family of sets `S_n ⊆ Bool^n` with bias at most `b_n = 1 / (n + 1)` on every
rectangle with both sides of size at least `K_n = (n + 1) ^ 3`, where `log K_n = o(n)` and
`b_n → 0`: the hypotheses of `AverageCaseBound` for the alphabet `Bool`, with a conclusion that
tends to `1/2`. -/
theorem exists_rectangleBias_family :
    ∃ S : ∀ n, Set (Fin n → Bool),
      (∀ᶠ n in atTop, RectangleBias (S n) ((n + 1) ^ 3) (1 / ((n : ℝ) + 1))) ∧
      (fun n : ℕ => Real.log (((n + 1) ^ 3 : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
  have hK (n : ℕ) :
      (Fintype.card (Fin n) + 1 : ℝ) ≤ (1 / ((n : ℝ) + 1)) ^ 2 * ((n + 1) ^ 3 : ℕ) := by
    rw [Fintype.card_fin]
    push_cast
    field_simp
    rfl
  choose S hS using fun n : ℕ => exists_rectangleBias (ι := Fin n) (by positivity) (hK n)
  refine ⟨S, Eventually.of_forall hS, ?_, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow, Nat.cast_ofNat] using
    (isLittleO_log_add 1).const_mul_left 3

end Cslib.Circuits.Frontier
