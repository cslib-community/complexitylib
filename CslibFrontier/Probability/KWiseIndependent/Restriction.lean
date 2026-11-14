/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
# Restriction-Fiber Cardinalities and Conditioning for `k`-Wise Independent Hash Families

This module provides exact natural-number fiber-cardinality identities for restrictions
`T.restrict (h i) = y` (`#T ≤ k`) and full evaluations `h i = y` (`Fintype.card X ≤ k`) of a
`k`-wise independent hash family `h : ι → X → Y`, together with fiber conditioning of a
`(k + 1)`-wise independent hash family on a single evaluation `h θ x = v₀`.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.card_filter_restrict_eq`: for `#T ≤ k` and `y : T → Y`
  with `[Nonempty Y]`,
  `Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} = Fintype.card ι`.
* `Cslib.Probability.IsKWiseIndependentHash.card_filter_eq_of_card_le`: for `Fintype.card X ≤ k` and
  `y : X → Y` with `[Nonempty Y]`,
  `#{i : ι | h i = y} * Fintype.card Y ^ Fintype.card X = Fintype.card ι`.
* `Cslib.Probability.IsKWiseIndependentHash.card_fiber_eq`: single-point fiber identity
  `Fintype.card Y * Fintype.card {θ // h θ x = v₀} = Fintype.card ι`.
* `Cslib.Probability.IsKWiseIndependentHash.fiber`: conditioning a `(k + 1)`-wise independent
  family on `h θ x = v₀` yields a nonempty fiber carrying a `k`-wise independent family on
  `{z : X // z ≠ x}`.
* `Cslib.Probability.dens_le_of_hash_fiber`: uniform fiber-wise upper bound on `(dens {θ | Bad θ})`
  under `(k + 1)`-wise independence by conditioning on `h θ x = v₀`.
-/

public section

namespace Cslib.Probability.IsKWiseIndependentHash

open Finset Fintype

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Exact natural-number fiber cardinality of `T.restrict (h i) = y` under a `k`-wise independent
hash family `h : ι → X → Y` over a nonempty codomain `Y`. -/
theorem card_filter_restrict_eq {k : ℕ} {h : ι → X → Y}
    (hh : IsKWiseIndependentHash k h) {T : Finset X} (hT : #T ≤ k) (y : T → Y) :
    Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} = Fintype.card ι := by
  have : Nonempty ι := hh.nonempty
  have hdens := hh.dens_filter_restrict_eq hT y
  rw [Finset.dens_eq_card_div_card] at hdens
  have hι_ne : (Fintype.card ι : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY_ne : ((Fintype.card Y : ℚ≥0) ^ #T) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hq :
      ((Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} : ℕ) : ℚ≥0) =
        (Fintype.card ι : ℚ≥0) := by
    push_cast
    rw [div_eq_iff hι_ne] at hdens
    rw [hdens, ← mul_assoc, mul_inv_cancel₀ hY_ne, one_mul]
  exact Nat.cast_inj.mp hq

/-- Exact natural-number fiber cardinality of `h i = y` on a finite domain `X` with
`Fintype.card X ≤ k` under a `k`-wise independent hash family `h : ι → X → Y`. -/
theorem card_filter_eq_of_card_le [Fintype X] {k : ℕ} {h : ι → X → Y}
    (hh : IsKWiseIndependentHash k h) (hX : Fintype.card X ≤ k) (y : X → Y) :
    #{i : ι | h i = y} * Fintype.card Y ^ Fintype.card X = Fintype.card ι := by
  let T : Finset X := Finset.univ
  have hT : #T ≤ k := by simpa [T] using hX
  have h1 := hh.card_filter_restrict_eq hT (fun a => y a.1)
  have hset :
      #{i : ι | T.restrict (h i) = fun a => y a.1} = #{i : ι | h i = y} := by
    congr 1
    ext i
    simp [T, funext_iff, Finset.restrict]
  have hT_card : #T = Fintype.card X := by simp [T]
  rw [hset, hT_card, Nat.mul_comm] at h1
  exact h1

/-- Exact single-point fiber cardinality `|Y| * |{θ // h θ x = v₀}| = |ι|` under `(k + 1)`-wise
independence. -/
theorem card_fiber_eq {k : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash (k + 1) h)
    (x : X) (v₀ : Y) :
    Fintype.card Y * Fintype.card {θ : ι // h θ x = v₀} = Fintype.card ι := by
  classical
  have hc := hh.card_filter_restrict_eq (T := {x}) (by simp) (fun _ => v₀)
  have hs : #{θ : ι | ({x} : Finset X).restrict (h θ) = fun _ => v₀} =
      Fintype.card {θ : ι // h θ x = v₀} := by
    rw [Fintype.card_subtype]; congr 1; ext θ; simp [funext_iff, Finset.restrict]
  rwa [Finset.card_singleton, pow_one, hs] at hc

/-- Conditioning a `(k + 1)`-wise independent hash family `h : ι → X → Y` on `h θ x = v₀` yields a
nonempty seed fiber `{θ : ι // h θ x = v₀}` carrying a `k`-wise independent hash family on
`{z : X // z ≠ x}`. -/
theorem fiber {k : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash (k + 1) h) (x : X) (v₀ : Y) :
    Nonempty {θ : ι // h θ x = v₀} ∧
    IsKWiseIndependentHash k
      (fun (θ : {θ : ι // h θ x = v₀}) (z : {z : X // z ≠ x}) => h θ.1 z.1) := by
  classical
  have : Nonempty ι := hh.nonempty
  have hcard1 : Fintype.card Y * Fintype.card {θ : ι // h θ x = v₀} = Fintype.card ι :=
    hh.card_fiber_eq x v₀
  have hF_pos : 0 < Fintype.card {θ : ι // h θ x = v₀} := by
    by_contra h0; have := Fintype.card_pos (α := ι)
    rw [Nat.eq_zero_of_not_pos h0, mul_zero] at hcard1; omega
  refine ⟨Fintype.card_pos_iff.mp hF_pos, ⟨fun {T} hT y => ?_⟩⟩
  let emb : {z : X // z ≠ x} ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  let T' : Finset X := Insert.insert x (T.map emb)
  have hmemT {a : X} (ha : a ≠ x) (hm : a ∈ T.map emb) : ⟨a, ha⟩ ∈ T := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hm; exact hu
  let y' : T' → Y := fun ⟨a, ha⟩ =>
    if hz : a = x then v₀ else y ⟨⟨a, hz⟩, hmemT hz ((Finset.mem_insert.mp ha).resolve_left hz)⟩
  have hcardT' := hh.card_filter_restrict_eq (T := T') (by simp [T', emb]; omega) y'
  have hbij : #{θ : {θ : ι // h θ x = v₀} | T.restrict (fun z => h θ.1 z.1) = y} =
      #{θ : ι | T'.restrict (h θ) = y'} := by
    refine Finset.card_bij (fun θ _ => θ.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
    · intro θ hθ; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext fun ⟨a, ha⟩ => ?_⟩
      rcases eq_or_ne a x with rfl | hzx
      · simp [Finset.restrict, y', θ.2]
      · simpa [Finset.restrict, y', hzx] using congrFun (Finset.mem_filter.mp hθ).2
          ⟨⟨a, hzx⟩, hmemT hzx ((Finset.mem_insert.mp ha).resolve_left hzx)⟩
    · intro θ hθ; rw [Finset.mem_filter] at hθ
      have hx0 : h θ x = v₀ := by
        simpa [Finset.restrict, y'] using congrFun hθ.2 ⟨x, Finset.mem_insert_self _ _⟩
      refine ⟨⟨θ, hx0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext fun w => ?_⟩, rfl⟩
      simpa [Finset.restrict, y', w.1.2] using
        congrFun hθ.2 ⟨w.1.1, Finset.mem_insert_of_mem (Finset.mem_map_of_mem emb w.2)⟩
  rw [show #T' = #T + 1 by simp [T', emb], pow_succ, mul_comm (Fintype.card Y ^ #T), mul_assoc,
    ← hbij, ← hcard1] at hcardT'
  rw [Finset.dens_eq_card_div_card, div_eq_iff (by exact_mod_cast hF_pos.ne'),
    eq_inv_mul_iff_mul_eq₀ (by positivity)]
  exact_mod_cast Nat.eq_of_mul_eq_mul_left Fintype.card_pos hcardT'

end Cslib.Probability.IsKWiseIndependentHash

namespace Cslib.Probability

open Finset Fintype

/-- Conditioning a `(k + 1)`-wise independent hash family `h` on `h θ x = v₀` yields a `k`-wise
independent family on `{y // y ≠ x}` (`IsKWiseIndependentHash.fiber`), bounding any seed event
uniformly across fibers. -/
theorem dens_le_of_hash_fiber {ι α Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {k : ℕ} {h : ι → α → Y} (hh : IsKWiseIndependentHash (k + 1) h) (x : α)
    (Bad : ι → Prop) [DecidablePred Bad] {B : ℝ}
    (hfib : ∀ v₀ : Y, ∀ (_ : Nonempty {θ : ι // h θ x = v₀}),
      IsKWiseIndependentHash k (fun (θ : {θ : ι // h θ x = v₀}) (y : {y : α // y ≠ x}) =>
        h θ.1 y.1) →
      (dens {θ : {θ : ι // h θ x = v₀} | Bad θ.1} : ℝ) ≤ B) :
    (dens {θ : ι | Bad θ} : ℝ) ≤ B := by
  classical
  have : Nonempty ι := hh.nonempty
  have hcard1 (v₀ : Y) : Fintype.card Y * Fintype.card {θ : ι // h θ x = v₀} = Fintype.card ι :=
    hh.card_fiber_eq x v₀
  rw [Finset.dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := ι))]
  have hY_ne : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpart : (#{θ : ι | Bad θ} : ℝ) = ∑ v₀ : Y, (#{θ : ι | Bad θ ∧ h θ x = v₀} : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (f := fun θ => h θ x) (s := {θ : ι | Bad θ})
      (t := Finset.univ) fun _ _ => Finset.mem_univ _).trans
      (Finset.sum_congr rfl fun v₀ _ => congrArg Finset.card (by ext θ; simp))
  have htot : (Fintype.card ι : ℝ) = ∑ v₀ : Y, (Fintype.card {θ : ι // h θ x = v₀} : ℝ) := by
    have hdiv (v₀ : Y) :
        (Fintype.card {θ : ι // h θ x = v₀} : ℝ) = Fintype.card ι / Fintype.card Y :=
      eq_div_of_mul_eq hY_ne (by rw [mul_comm]; exact_mod_cast hcard1 v₀)
    simp_rw [hdiv]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hY_ne]
  rw [hpart, htot, Finset.mul_sum]; refine Finset.sum_le_sum fun v₀ _ => ?_
  obtain ⟨hne_v₀, hind_v₀⟩ := hh.fiber x v₀
  have hF_pos : 0 < Fintype.card {θ : ι // h θ x = v₀} := Fintype.card_pos
  have hf := hfib v₀ hne_v₀ hind_v₀
  rw [Finset.dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    div_le_iff₀ (by exact_mod_cast hF_pos)] at hf
  rwa [show #{θ : {θ : ι // h θ x = v₀} | Bad θ.1} = #{θ : ι | Bad θ ∧ h θ x = v₀} from
    Finset.card_bij (fun θ _ => θ.1)
      (fun θ hθ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hθ).2, θ.2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun θ hθ => ⟨⟨θ, (Finset.mem_filter.mp hθ).2.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hθ).2.1⟩, rfl⟩)] at hf

end Cslib.Probability
