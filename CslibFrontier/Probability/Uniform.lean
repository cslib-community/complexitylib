/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Uniform sampling and subset sums

A surjective additive homomorphism between finite groups preserves the uniform distribution.
In particular, translating a uniform group element by a fixed mask leaves it uniform (the
one-time pad).
Consequently, the sum over any nonempty subset of independently uniform group elements is
uniform, and two distinct nonempty subsets give independent uniform sums.
Replacing any one summand by a fresh uniform value also makes the complete sum uniform.

For bitstrings, addition is pointwise XOR. These subset sums are the pairwise independent
masks used by the Goldreich–Levin decoder. The joint-distribution theorem does not assert
mutual independence of three or more subset sums. The fiber-counting criterion is shared with
`PairwiseIndependentHash.Shift`; the subset-sum results are adapted from the cslib `crypto`
branch at `5ff69ca`.

## Main results

* `Cslib.Probability.card_mul_card_filter_eq_of_shift`,
  `Cslib.Probability.dens_filter_eq_of_shift`: translations force equal fibers.
* `Cslib.Probability.PMF.uniformOfFintype_map_of_shift`,
  `Cslib.Probability.PMF.uniformOfFintype_map_addHom`,
  `Cslib.Probability.PMF.uniformOfFintype_map_monoidHom`: uniformity from translations, in
  particular for surjective homomorphisms.
* `Cslib.Probability.PMF.uniformOfFintype_map_add_right`,
  `Cslib.Probability.PMF.uniformOfFintype_map_add_left`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_add_right`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_add_left`: a fixed mask leaves a uniform group
  element uniform (the one-time pad).
* `Cslib.Probability.PMF.uniformOfFintype_map_comp`: a uniform function read through an injection
  is uniform.
* `Cslib.Probability.PMF.uniformOfFintype_map_sum`,
  `Cslib.Probability.PMF.uniformOfFintype_map_sum_pair`: subset sums are uniform and pairwise
  independent.

## References

* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]
-/

public section

namespace Cslib.Probability

open Finset
open scoped ENNReal

section Fiber

variable {ι G : Type*} [Fintype ι] [AddGroup G] [Fintype G] [DecidableEq G]

/-- If every translate `f + c` of a function `f : ι → G` into a finite group is `f ∘ e` for a
permutation `e` of `ι`, then all fibers of `f` have the same size `|ι| / |G|`. -/
theorem card_mul_card_filter_eq_of_shift {f : ι → G}
    (hf : ∀ c : G, ∃ e : Equiv.Perm ι, ∀ i, f (e i) = f i + c) (y : G) :
    Fintype.card G * #{i | f i = y} = Fintype.card ι := by
  have hfib (z : G) : #{i | f i = z} = #{i | f i = y} := by
    obtain ⟨e, he⟩ := hf (-z + y)
    refine card_equiv e fun i => ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [he, ← add_assoc, add_eq_right, add_neg_eq_zero]
  have hsum := card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) fun _ _ => mem_univ _
  rw [card_univ] at hsum
  rw [hsum]
  simp only [hfib, sum_const, card_univ, smul_eq_mul]

/-- **Uniformity from shifts**: if every translate `f + c` of a function `f : ι → G` into a
finite group is `f ∘ e` for a permutation `e` of `ι`, then `f` is uniformly distributed: for a
uniformly random `i`, `f i` takes each value with probability `1 / |G|`. -/
theorem dens_filter_eq_of_shift [Nonempty ι] {f : ι → G}
    (hf : ∀ c : G, ∃ e : Equiv.Perm ι, ∀ i, f (e i) = f i + c) (y : G) :
    dens {i | f i = y} = (Fintype.card G : ℚ≥0)⁻¹ := by
  have h := card_mul_card_filter_eq_of_shift hf y
  have hpos : #{i | f i = y} ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at h
    exact Fintype.card_ne_zero h.symm
  rw [dens_eq_card_div_card, ← h, Nat.cast_mul, div_mul_cancel_right₀ (Nat.cast_ne_zero.2 hpos)]

end Fiber

namespace PMF

/-- A function whose output translations are realized by permutations of its input sends
uniform inputs to uniform outputs. -/
theorem uniformOfFintype_map_of_shift {ι G : Type*}
    [Fintype ι] [Nonempty ι] [AddGroup G] [Fintype G] {f : ι → G}
    (hf : ∀ c : G, ∃ e : Equiv.Perm ι, ∀ i, f (e i) = f i + c) :
    (PMF.uniformOfFintype ι).map f = PMF.uniformOfFintype G := by
  classical
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_uniformOfFintype_map_apply, dens_filter_eq_of_shift hf]
  simp

section Mask

variable {G : Type*} [AddGroup G] [Fintype G]

/-- **One-time pad**: translating a uniform element of a finite group on the right by a fixed
mask leaves it uniform. -/
theorem uniformOfFintype_map_add_right (c : G) :
    (PMF.uniformOfFintype G).map (· + c) = PMF.uniformOfFintype G :=
  uniformOfFintype_map_equiv (Equiv.addRight c)

/-- **One-time pad**: translating a uniform element of a finite group on the left by a fixed mask
leaves it uniform. -/
theorem uniformOfFintype_map_add_left (c : G) :
    (PMF.uniformOfFintype G).map (c + ·) = PMF.uniformOfFintype G :=
  uniformOfFintype_map_equiv (Equiv.addLeft c)

/-- Masking a uniform draw on the right does not change an experiment that consumes it. -/
theorem uniformOfFintype_bind_add_right {β : Type*} (c : G) (f : G → PMF β) :
    (PMF.uniformOfFintype G).bind (fun x => f (x + c)) = (PMF.uniformOfFintype G).bind f := by
  conv_rhs => rw [← uniformOfFintype_map_add_right c, PMF.bind_map]
  rfl

/-- Masking a uniform draw on the left does not change an experiment that consumes it. -/
theorem uniformOfFintype_bind_add_left {β : Type*} (c : G) (f : G → PMF β) :
    (PMF.uniformOfFintype G).bind (fun x => f (c + x)) = (PMF.uniformOfFintype G).bind f := by
  conv_rhs => rw [← uniformOfFintype_map_add_left c, PMF.bind_map]
  rfl

end Mask

/-- A uniform function read through an injection is uniform. -/
theorem uniformOfFintype_map_comp {S Q R : Type*} [Fintype S] [DecidableEq S] [Fintype Q]
    [DecidableEq Q] [Fintype R] [Nonempty R] [AddCommGroup R] {g : S → Q}
    (hg : Function.Injective g) :
    (PMF.uniformOfFintype (Q → R)).map (fun f => f ∘ g) = PMF.uniformOfFintype (S → R) := by
  classical
  refine uniformOfFintype_map_of_shift fun c => ⟨Equiv.addRight
    (Function.extend g c 0), fun f => funext fun s => ?_⟩
  simp [hg.extend_apply]

/-- A finite sum is uniform if any one summand is fresh uniform, regardless of the others. -/
theorem uniformOfFintype_map_sum_update {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G] (values : ι → G) (i : ι) :
    (PMF.uniformOfFintype G).map (fun value => ∑ j, Function.update values i value j) =
      PMF.uniformOfFintype G := by
  simp only [Finset.sum_update_of_mem (Finset.mem_univ i)]
  exact uniformOfFintype_map_add_right _

/-- A surjective additive homomorphism of finite groups sends uniform inputs to uniform outputs. -/
theorem uniformOfFintype_map_addHom {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype G).map f = PMF.uniformOfFintype H := by
  apply uniformOfFintype_map_of_shift
  intro c
  obtain ⟨g, rfl⟩ := hf c
  exact ⟨Equiv.addRight g, fun a => f.map_add a g⟩

/-- A surjective homomorphism of finite groups sends uniform inputs to uniform outputs. -/
theorem uniformOfFintype_map_monoidHom {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype G).map f = PMF.uniformOfFintype H := by
  rw [← uniformOfFintype_map_equiv (Additive.toMul : Additive G ≃ G), PMF.map_comp,
    ← uniformOfFintype_map_equiv (Additive.toMul : Additive H ≃ H),
    ← uniformOfFintype_map_addHom (MonoidHom.toAdditive f) hf, PMF.map_comp]
  rfl

private theorem sumPair_surjective_of_mem_notMem {ι G : Type*}
    [AddCommGroup G] (s t : Finset ι) {i : ι}
    (hi : i ∈ s) (hit : i ∉ t) (ht : t.Nonempty) :
    Function.Surjective (fun masks : ι → G => (∑ j ∈ s, masks j, ∑ j ∈ t, masks j)) := by
  classical
  obtain ⟨j, hj⟩ := ht
  rintro ⟨a, b⟩
  refine ⟨Pi.single i (a - if j ∈ s then b else 0) + Pi.single j b, ?_⟩
  ext <;> simp [Finset.sum_add_distrib, Finset.sum_pi_single', hi, hit, hj]

private theorem sumPair_surjective {ι G : Type*}
    [AddCommGroup G] (s t : Finset ι)
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ≠ t) :
    Function.Surjective (fun masks : ι → G => (∑ j ∈ s, masks j, ∑ j ∈ t, masks j)) := by
  classical
  by_cases hsub : s ⊆ t
  · have hex : ∃ i ∈ t, i ∉ s := by
      by_contra h
      apply hst
      apply Finset.Subset.antisymm hsub
      simpa [Finset.subset_iff] using h
    obtain ⟨i, hit, his⟩ := hex
    intro pair
    obtain ⟨masks, h⟩ :=
      sumPair_surjective_of_mem_notMem (G := G) t s hit his hs (pair.2, pair.1)
    exact ⟨masks, Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)⟩
  · obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hsub
    exact sumPair_surjective_of_mem_notMem s t his hit ht

/-- A nonempty subset sum of independent uniform group elements is uniform. -/
theorem uniformOfFintype_map_sum {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G]
    (s : Finset ι) (hs : s.Nonempty) :
    (PMF.uniformOfFintype (ι → G)).map (fun masks => ∑ i ∈ s, masks i) =
      PMF.uniformOfFintype G := by
  classical
  let f : (ι → G) →+ G := {
    toFun := fun masks => ∑ i ∈ s, masks i
    map_zero' := by simp
    map_add' := by intros; simp [Finset.sum_add_distrib] }
  apply uniformOfFintype_map_addHom f
  obtain ⟨i, hi⟩ := hs
  intro a
  exact ⟨Pi.single i a, by simp [f, hi]⟩

/-- Distinct nonempty subset sums have the joint distribution of two independent uniform samples. -/
theorem uniformOfFintype_map_sum_pair {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G]
    (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ≠ t) :
    (PMF.uniformOfFintype (ι → G)).map
        (fun masks => (∑ i ∈ s, masks i, ∑ i ∈ t, masks i)) =
      PMF.uniformOfFintype (G × G) := by
  let f : (ι → G) →+ G × G := {
    toFun := fun masks => (∑ i ∈ s, masks i, ∑ i ∈ t, masks i)
    map_zero' := by simp
    map_add' := by intros; simp [Finset.sum_add_distrib] }
  exact uniformOfFintype_map_addHom f (sumPair_surjective s t hs ht hst)

end PMF

end Cslib.Probability
