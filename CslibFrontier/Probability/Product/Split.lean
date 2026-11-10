/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product.Reindex

/-!
# Splitting the coordinates of a finite product

Split the coordinates of an independent product by a predicate `P`, along Mathlib's
`Equiv.piEquivPiSubtypeProd`. The coordinates satisfying `P` and the remaining coordinates form two
independent products. In particular, the restriction of an independent product to some of its
coordinates, or its composition with an injection of index types, is again an independent product.
Conditioning a uniform tuple on the value of one coordinate splits that coordinate off: it becomes
constant, and the other coordinates stay uniform.

## Main results

* `Cslib.Probability.PMF.pi_map_piEquivPiSubtypeProd`: the two parts of a split product are
  independent products.
* `Cslib.Probability.PMF.pi_map_restrict`, `Cslib.Probability.PMF.pi_map_comp_injective`:
  restricting an independent product, or reading it along an injection, gives the independent
  product of the selected factors.
* `Cslib.Probability.PMF.filter_uniformOfFintype_eval_eq`: conditioning a uniform tuple on one
  coordinate sets that coordinate.
-/

public section

namespace Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]

/-- Splitting the coordinates of an independent product by a predicate `P` gives two independent
products: one over the coordinates satisfying `P`, one over the rest. -/
theorem pi_map_piEquivPiSubtypeProd (P : ι → Prop) [DecidablePred P] (p : ∀ i, PMF (α i)) :
    (pi p).map (Equiv.piEquivPiSubtypeProd P α) =
      (pi fun i : {i // P i} => p i).bind fun a =>
        (pi fun i : {i // ¬P i} => p i).map (a, ·) := by
  ext ⟨a, b⟩
  rw [map_equiv_apply, bind_map_prodMk_apply, pi_apply, pi_apply, pi_apply,
    ← Fintype.prod_subtype_mul_prod_subtype P]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  · simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]

/-- Restricting an independent product to the coordinates satisfying `P` gives the independent
product of those coordinates. -/
theorem pi_map_restrict (P : ι → Prop) [DecidablePred P] (p : ∀ i, PMF (α i)) :
    (pi p).map (fun a (i : {i // P i}) => a i) = pi fun i : {i // P i} => p i := by
  have h := congrArg (PMF.map Prod.fst) (pi_map_piEquivPiSubtypeProd P p)
  rw [PMF.map_comp, PMF.map_bind] at h
  have hc (a : ∀ i : {i // P i}, α i) :
      ((pi fun i : {i // ¬P i} => p i).map (a, ·)).map Prod.fst = PMF.pure a := by
    rw [PMF.map_comp]
    exact PMF.map_const _ a
  simp only [hc, PMF.bind_pure] at h
  exact h

/-- Reading an independent product along an equivalence `e` onto the coordinates satisfying `P`
gives the independent product of the factors along `e`. -/
theorem pi_map_comp_subtypeEquiv {κ : Type*} [Fintype κ] (P : ι → Prop) (p : ∀ i, PMF (α i))
    (e : κ ≃ {i // P i}) :
    (pi p).map (fun a k => a (e k)) = pi fun k => p (e k) := by
  classical
  have h := pi_map_piCongrLeft_symm (fun i : {i // P i} => p i) e
  rw [← pi_map_restrict P, PMF.map_comp] at h
  exact h

/-- Reading an independent product along an injection `e` of index types gives the independent
product of the factors along `e`: the coordinates `a (e k)` are independent with laws `p (e k)`. -/
theorem pi_map_comp_injective {κ : Type*} [Fintype κ] (p : ∀ i, PMF (α i)) {e : κ → ι}
    (he : Function.Injective e) :
    (pi p).map (fun a k => a (e k)) = pi fun k => p (e k) :=
  pi_map_comp_subtypeEquiv (· ∈ Set.range e) p (Equiv.ofInjective e he)

/-- Conditioning a uniform tuple on the value `c` of its coordinate `j` sets that coordinate to `c`
and keeps the other coordinates uniform. -/
theorem filter_uniformOfFintype_eval_eq [DecidableEq ι] {γ : Type*} [Fintype γ] [Nonempty γ]
    (j : ι) (c : γ) (h : ∃ d ∈ {d : ι → γ | d j = c}, d ∈ (uniformOfFintype (ι → γ)).support) :
    (uniformOfFintype (ι → γ)).filter {d | d j = c} h =
      (uniformOfFintype (ι → γ)).map (Function.update · j c) := by
  set U := uniformOfFintype (ι → γ)
  -- Draw the value of coordinate `j` first, then the tuple with that value at `j`.
  have hpair : U.map (fun d => (d j, d)) =
      (uniformOfFintype γ).bind fun c' => (U.map (Function.update · j c')).map (c', ·) := by
    rw [← PMF.bind_pure_comp, bind_uniformOfFintype_update j]
    simp only [Function.comp_apply, Function.update_self, PMF.map_comp, Function.comp_def]
    rfl
  have hc : ∃ a ∈ ({c} : Set γ), a ∈ (uniformOfFintype γ).support :=
    ⟨c, rfl, mem_support_uniformOfFintype c⟩
  have hpure : (uniformOfFintype γ).filter {c} hc = PMF.pure c := by
    ext a
    rw [PMF.filter_apply, PMF.pure_apply, ← PMF.toOuterMeasure_apply,
      PMF.toOuterMeasure_apply_singleton]
    by_cases ha : a = c
    · rw [ha, Set.indicator_of_mem rfl, ite_eq_left rfl, ENNReal.mul_inv_cancel
        ((PMF.mem_support_iff _ _).mp (mem_support_uniformOfFintype c)) (PMF.apply_ne_top _ _)]
    · rw [Set.indicator_of_notMem ha, ite_eq_right ha, zero_mul]
  obtain ⟨d, hd, hdU⟩ := h
  have hw : ∃ z ∈ Prod.fst ⁻¹' ({c} : Set γ), z ∈ (U.map fun d => (d j, d)).support :=
    ⟨(d j, d), hd, (PMF.mem_support_map_iff _ _ _).mpr ⟨d, hdU, rfl⟩⟩
  have hw' := hpair ▸ hw
  have hcongr : ∀ (p q : PMF (γ × (ι → γ))) (_ : p = q) hp hq,
      p.filter (Prod.fst ⁻¹' {c}) hp = q.filter (Prod.fst ⁻¹' {c}) hq := by
    rintro p q rfl hp hq
    rfl
  have hfilter := (filter_map U (fun d => (d j, d)) _ hw ⟨d, hd, hdU⟩).symm.trans
    ((hcongr _ _ hpair hw hw').trans (filter_bind_pair _ _ _ hw' hc))
  rw [hpure, PMF.pure_bind] at hfilter
  have h2 := congrArg (PMF.map Prod.snd) hfilter
  simp only [PMF.map_comp, Function.comp_def] at h2
  exact (PMF.map_id _).symm.trans h2

end Cslib.Probability.PMF
