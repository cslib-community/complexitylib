/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Parity is far from low-degree functions

Over a field `F` in which `2` is invertible, a function of degree at most `D` agrees with the parity
of all `|ι|` coordinates on at most as many inputs as there are sets of at most `|ι| / 2 + D`
coordinates (`BitString.card_agree_parityOn_univ_le`) [Smolensky1987]. The proof works with the
characters `chi F S`, the products of the signs `(-1) ^ xᵢ = 1 - 2 xᵢ` over the sets `S`, with
values in `F`: the parity of all coordinates, read as a sign, is the character of `univ`
(`BitString.chi_eq_neg_one_pow_parityOn`), and characters square to `1`. So on the inputs where a
function `P` of degree `D` agrees with parity, a character of more than `|ι| / 2` coordinates
equals `1 - 2 P` times the character of the other coordinates, of degree at most `|ι| / 2 + D`.
Every function on these inputs therefore agrees with one of degree at most `|ι| / 2 + D`
(`BitString.exists_agree_of_parity`), and comparing dimensions bounds the number of inputs
(`BitString.card_le_of_forall_exists_agree`).

## Main results

* `Cslib.BitString.exists_agree_of_parity`, `Cslib.BitString.card_le_of_forall_exists_agree`:
  if `Q` of degree `D` agrees with the full character on `G`, every function on `G` agrees with one
  of degree at most `|ι| / 2 + D`, bounding `#G`.
* `Cslib.BitString.card_agree_parityOn_univ_le`, `Cslib.BitString.card_agree_parity_le`: parity
  is far from low-degree functions.

## References

* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib.BitString

open Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- If `Q` has degree at most `D` and agrees with the character of all coordinates on `G`, every
function agrees on `G` with a function of degree at most `|ι| / 2 + D`. -/
theorem exists_agree_of_parity [Invertible (2 : F)] {D : ℕ} {Q : (ι → Bool) → F}
    (hQ : Q ∈ lowDegree F ι D) (G : Finset (ι → Bool))
    (hG : ∀ x ∈ G, Q x = chi F univ x) (f : (ι → Bool) → F) :
    ∃ p ∈ lowDegree F ι (Fintype.card ι / 2 + D), ∀ x ∈ G, p x = f x := by
  classical
  have hf : f ∈ signSpan F ι (Fintype.card ι) :=
    lowDegree_le_signSpan _ (mem_lowDegree_self f)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, -, rfl⟩ := hg
    by_cases hS : #S ≤ Fintype.card ι / 2
    · exact ⟨chi F S, lowDegree_mono (by omega) (chi_mem_lowDegree S), fun _ _ => rfl⟩
    · refine ⟨Q * chi F Sᶜ, ?_, fun x hx => ?_⟩
      · have hc : #Sᶜ ≤ Fintype.card ι / 2 := by
          rw [card_compl]
          omega
        exact lowDegree_mono (by omega) (mul_mem_lowDegree hQ (chi_mem_lowDegree Sᶜ))
      · rw [Pi.mul_apply, hG x hx, ← union_compl S, chi_union disjoint_compl_right, mul_assoc,
          chi_mul_self, mul_one]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpx⟩ := hf
    obtain ⟨q, hq, hqx⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x hx => by simp [hpx x hx, hqx x hx]⟩
  | smul c f _ hf =>
    obtain ⟨p, hp, hpx⟩ := hf
    exact ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => by simp [hpx x hx]⟩

/-- If every function agrees on `G` with a function of degree at most `H`, then `G` has at most as
many points as there are sets of at most `H` coordinates. -/
theorem card_le_of_forall_exists_agree {H : ℕ} (G : Finset (ι → Bool))
    (hG : ∀ f : (ι → Bool) → F, ∃ p ∈ lowDegree F ι H, ∀ x ∈ G, p x = f x) :
    #G ≤ #{S : Finset ι | #S ≤ H} := by
  classical
  -- restricting to `G` is onto
  let restrict : lowDegree F ι H →ₗ[F] (G → F) :=
    { toFun := fun p x => p.1 x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective restrict := fun g => by
    obtain ⟨p, hp, hpx⟩ := hG fun x => if hx : x ∈ G then g ⟨x, hx⟩ else 0
    refine ⟨⟨p, hp⟩, funext fun x => ?_⟩
    change p x.1 = g x
    simpa using hpx x.1 x.2
  have h := LinearMap.finrank_range_le restrict
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h
  exact h.trans (finrank_lowDegree_le H)

/-- **Parity is far from low-degree functions.** A function of degree at most `D` agrees with the
parity of all coordinates on at most as many inputs as there are sets of at most `|ι| / 2 + D`
coordinates. -/
theorem card_agree_parityOn_univ_le [DecidableEq ι] [DecidableEq F] [Invertible (2 : F)] {D : ℕ}
    {P : (ι → Bool) → F} (hP : P ∈ lowDegree F ι D) :
    #{x | P x = bitVal F (parityOn univ x)} ≤
      #{S : Finset ι | #S ≤ Fintype.card ι / 2 + D} :=
  card_le_of_forall_exists_agree _ (exists_agree_of_parity (Q := 1 - 2 • P)
    (Submodule.sub_mem _ (one_mem_lowDegree D) (Submodule.smul_of_tower_mem _ 2 hP))
    {x | P x = bitVal F (parityOn univ x)} fun x hx => by
      rw [mem_filter] at hx
      rw [chi_eq_neg_one_pow_parityOn, neg_one_pow_toNat_eq_one_sub_two_mul_bitVal, ← hx.2]
      simp [two_mul])

/-- **Parity is far from low-degree functions.** A function of degree at most `D` agrees with
parity on at most as many inputs as there are sets of at most `n / 2 + D` coordinates. -/
theorem card_agree_parity_le [DecidableEq F] [Invertible (2 : F)] {n D : ℕ}
    {P : BitString n → F} (hP : P ∈ lowDegree F (Fin n) D) :
    #{x | P x = bitVal F (parity n x)} ≤ #{S : Finset (Fin n) | #S ≤ n / 2 + D} := by
  have h := card_agree_parityOn_univ_le hP
  rw [Fintype.card_fin] at h
  exact h

end Cslib.BitString
