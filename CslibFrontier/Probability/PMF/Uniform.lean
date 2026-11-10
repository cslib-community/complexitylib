/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
public import Mathlib.Data.Fintype.Pi

/-!
# Uniform distributions and resampling

Every value of a nonempty finite type has positive uniform mass (`mem_support_uniformOfFintype`),
and the uniform probability or measure of an event under `uniformOfFinset` or `uniformOfFintype` is
the fraction of members in the event (`toOuterMeasure_uniformOfFinset`,
`toOuterMeasure_uniformOfFinset_toReal`, `toMeasure_uniformOfFinset`,
`toOuterMeasure_uniformOfFintype`, `toOuterMeasure_uniformOfFintype_toReal`,
`toMeasure_uniformOfFintype`).

Draw `a` uniformly from `α` and, independently, `b` uniformly from `β`. For any equivalence
`e : α × β ≃ γ × δ`, the pair `e (a, b)` is uniform on `γ × δ`, so its first component is uniform
on `γ` (`uniformOfFintype_bind_map_fst_equiv`). This is the resampling step of hybrid arguments:
overwriting part of a uniform string `a` by independent uniform values `b` leaves it uniform, since
the overwritten string and the old part together determine `(a, b)`.

## Main results

* `Cslib.Probability.PMF.mem_support_uniformOfFintype`: every value has positive uniform mass.
* `Cslib.Probability.PMF.uniformOfFintype_finset_map_val`: subtype and finite-set uniform
  laws agree.
* `Cslib.Probability.PMF.uniformOfFintype_bind_equiv`: reparametrizing a uniform draw by a
  bijection leaves an experiment unchanged.
* `Cslib.Probability.PMF.uniformOfFintype_prod_map_fst`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_map`: the first component of a uniform pair is
  uniform, and mapping over two independent uniform draws is mapping over a uniform pair.
* `Cslib.Probability.PMF.uniformOfFintype_pi_map_restrict`,
  `Cslib.Probability.PMF.uniformOfFintype_pi_bind_restrict`: restricting a uniform dependent
  function to a finite subset gives the uniform distribution on that subset.
* `Cslib.Probability.PMF.uniformOfFintype_bind_bind_adaptiveUpdate`: resampling the value at a
  point chosen from the function itself.
* `Cslib.Probability.PMF.uniformOfFintype_bind_map_fst_equiv`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_bind_fst_equiv`: resampling along an equivalence.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFinset`,
  `Cslib.Probability.PMF.toOuterMeasure_uniformOfFinset_toReal`,
  `Cslib.Probability.PMF.toMeasure_uniformOfFinset`,
  `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype`,
  `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal`,
  `Cslib.Probability.PMF.toMeasure_uniformOfFintype`: the uniform probability of an
  event is the fraction of its members.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β γ δ ε : Type*}

section Uniform

/-- Every value of a nonempty finite type is in the uniform distribution's support. -/
theorem mem_support_uniformOfFintype [Fintype α] [Nonempty α] (a : α) :
    a ∈ (uniformOfFintype α).support := by
  simp [uniformOfFintype]

/-- Forgetting membership proofs in a uniform draw from a finset subtype gives its uniform
finite-set law. -/
theorem uniformOfFintype_finset_map_val (s : Finset α) [Nonempty s] :
    (uniformOfFintype s).map Subtype.val =
      uniformOfFinset s (Finset.nonempty_coe_sort.mp inferInstance) := by
  classical
  ext a
  simp only [PMF.map_apply, uniformOfFintype_apply, uniformOfFinset_apply, Fintype.card_coe]
  erw [tsum_subtype (↑s : Set α) (fun x => if a = x then (s.card : ℝ≥0∞)⁻¹ else 0)]
  rw [tsum_eq_single a]
  · simp [Set.indicator_apply]
  · intro b hb
    simp [Set.indicator_apply, Ne.symm hb]

-- Moved from `CslibFrontier/Crypto/Computational/DiffieHellman.lean` (Samuel Schlesinger), where
-- it was private, so that the garbling and Diffie–Hellman modules share one statement.
/-- Reparametrizing a uniform draw by a bijection does not change an experiment. -/
theorem uniformOfFintype_bind_equiv [Fintype α] [Nonempty α] (e : α ≃ α) (f : α → PMF β) :
    (uniformOfFintype α).bind (fun a => f (e a)) = (uniformOfFintype α).bind f := by
  change (uniformOfFintype α).bind (f ∘ e) = (uniformOfFintype α).bind f
  rw [← PMF.bind_map, uniformOfFintype_map_equiv]

variable [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- The first component of a uniform pair is uniform. -/
theorem uniformOfFintype_prod_map_fst :
    (uniformOfFintype (α × β)).map Prod.fst = uniformOfFintype α := by
  rw [← uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  calc _ = (uniformOfFintype α).bind PMF.pure := by
        congr 1 with a : 1
        exact PMF.map_const _ _
    _ = _ := PMF.bind_pure _

/-- Mapping a curried binary function over two independent uniform draws is equivalent to
mapping the uncurried function over a uniform pair. Iterating this rewrite collapses `n`-ary
chains of independent uniform draws into a single `uniformOfFintype` over a nested product. -/
theorem uniformOfFintype_bind_map (f : α → β → γ) :
    ((uniformOfFintype α).bind fun a => (uniformOfFintype β).map fun b => f a b) =
      (uniformOfFintype (α × β)).map (fun p => f p.1 p.2) := by
  rw [← uniformOfFintype_prod, PMF.map_bind]
  simp [PMF.map_comp, Function.comp_def]

/-- Restricting a uniform dependent function on `ι` to `I : Finset ι` gives the uniform
distribution on `(i : I) → π i`. -/
theorem uniformOfFintype_pi_map_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] [∀ i, Nonempty (π i)] (I : Finset ι) :
    (uniformOfFintype (∀ i, π i)).map I.restrict = uniformOfFintype ((i : I) → π i) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) π
  calc (uniformOfFintype (∀ i, π i)).map I.restrict
      = ((uniformOfFintype (∀ i, π i)).map e).map Prod.fst := by
          rw [PMF.map_comp]; rfl
    _ = (uniformOfFintype (((i : I) → π i) × ((j : {j // j ∉ I}) → π j))).map Prod.fst := by
          rw [uniformOfFintype_map_equiv e]
    _ = uniformOfFintype ((i : I) → π i) := uniformOfFintype_prod_map_fst

/-- Binding a uniform dependent function on `ι` to a continuation that depends only on its
restriction to `I : Finset ι` is equivalent to sampling uniformly on `(i : I) → π i`. -/
theorem uniformOfFintype_pi_bind_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] [∀ i, Nonempty (π i)]
    (I : Finset ι) (f : ((i : I) → π i) → PMF ε) :
    ((uniformOfFintype (∀ i, π i)).bind fun a => f (I.restrict a)) =
      (uniformOfFintype ((i : I) → π i)).bind f := by
  rw [← uniformOfFintype_pi_map_restrict I, PMF.bind_map]
  rfl

variable [Fintype γ] [Nonempty γ] [Finite δ]

/-- **Resampling**: for independent uniform `a` and `b` and an equivalence `e : α × β ≃ γ × δ`,
the first component of `e (a, b)` is uniform. -/
theorem uniformOfFintype_bind_map_fst_equiv (e : α × β ≃ γ × δ) :
    ((uniformOfFintype α).bind fun a => (uniformOfFintype β).map fun b => (e (a, b)).1) =
      uniformOfFintype γ := by
  have : Fintype δ := Fintype.ofFinite δ
  have : Nonempty δ := ⟨(e (Classical.arbitrary _)).2⟩
  calc _ = (uniformOfFintype (α × β)).map (Prod.fst ∘ e) := by
        rw [← uniformOfFintype_prod, PMF.map_bind]
        simp only [PMF.map_comp]
        rfl
    _ = (uniformOfFintype (γ × δ)).map Prod.fst := by
        rw [← PMF.map_comp, uniformOfFintype_map_equiv]
    _ = _ := uniformOfFintype_prod_map_fst

/-- **Resampling** inside an experiment: running `f` on the first component of `e (a, b)`, for
independent uniform `a` and `b`, is running `f` on a uniform input. -/
theorem uniformOfFintype_bind_bind_fst_equiv (e : α × β ≃ γ × δ) (f : γ → PMF ε) :
    ((uniformOfFintype α).bind fun a => (uniformOfFintype β).bind fun b => f (e (a, b)).1) =
      (uniformOfFintype γ).bind f := by
  rw [← uniformOfFintype_bind_map_fst_equiv e]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

/-- **Adaptive resampling**: a uniform function whose value at a point `p f`, chosen from the
function itself, is replaced by a fresh uniform value is uniform, provided that replacing that
value does not move the point. `(f, v) ↦ (Function.update f (p f) v, f (p f))` is an involution. -/
theorem uniformOfFintype_bind_bind_adaptiveUpdate {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (p : (ι → κ) → ι)
    (hp : ∀ f v, p (Function.update f (p f) v) = p f) (g : (ι → κ) → PMF ε) :
    ((uniformOfFintype (ι → κ)).bind fun f =>
      (uniformOfFintype κ).bind fun v => g (Function.update f (p f) v)) =
      (uniformOfFintype (ι → κ)).bind g := by
  let swap : (ι → κ) × κ → (ι → κ) × κ := fun fv =>
    (Function.update fv.1 (p fv.1) fv.2, fv.1 (p fv.1))
  have hswap : Function.Involutive swap := by
    rintro ⟨f, v⟩
    simp only [swap, hp, Function.update_self, Function.update_idem, Function.update_eq_self]
  exact uniformOfFintype_bind_bind_fst_equiv hswap.toPerm g

end Uniform

/-- The uniform distribution on a nonempty finite set gives an event the fraction of the set's
members in the event, as an extended nonnegative real. -/
theorem toOuterMeasure_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (event : Set α)
    [DecidablePred (· ∈ event)] :
    (uniformOfFinset s hs).toOuterMeasure event =
      (s.filter (· ∈ event)).card * (s.card : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply, tsum_eq_sum (s := s)]
  · simp only [Set.indicator_apply, uniformOfFinset_apply]
    rw [← Finset.sum_filter,
      Finset.sum_congr (g := fun _ => (s.card : ℝ≥0∞)⁻¹) rfl
        fun x hx => by simp [Finset.mem_of_mem_filter x hx],
      Finset.sum_const, nsmul_eq_mul]
  · intro x hx
    simp [Set.indicator_apply, uniformOfFinset_apply, hx]

/-- The probability of an event under the uniform distribution on a nonempty finite set is the
fraction of the set's members in the event. -/
theorem toOuterMeasure_uniformOfFinset_toReal (s : Finset α) (hs : s.Nonempty) (event : Set α)
    [DecidablePred (· ∈ event)] :
    ((uniformOfFinset s hs).toOuterMeasure event).toReal =
      (s.filter (· ∈ event)).card / s.card := by
  rw [toOuterMeasure_uniformOfFinset, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]

/-- The measure of a measurable event under the uniform distribution on a nonempty finite set is
the fraction of the set's members in the event. -/
theorem toMeasure_uniformOfFinset [MeasurableSpace α] (s : Finset α) (hs : s.Nonempty)
    {event : Set α} [DecidablePred (· ∈ event)] (he : MeasurableSet event) :
    (uniformOfFinset s hs).toMeasure event =
      (s.filter (· ∈ event)).card * (s.card : ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ he, toOuterMeasure_uniformOfFinset]

/-- The uniform distribution on a finite type gives an event the fraction of its members, as an
extended nonnegative real. -/
theorem toOuterMeasure_uniformOfFintype [Fintype α] [Nonempty α] (event : Set α)
    [DecidablePred (· ∈ event)] :
    (uniformOfFintype α).toOuterMeasure event =
      (Finset.univ.filter (· ∈ event)).card * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simpa [uniformOfFintype] using
    toOuterMeasure_uniformOfFinset Finset.univ Finset.univ_nonempty event

/-- The probability of an event under the uniform distribution on a finite type is the fraction
of its members. -/
theorem toOuterMeasure_uniformOfFintype_toReal [Fintype α] [Nonempty α] (event : Set α)
    [DecidablePred (· ∈ event)] :
    ((uniformOfFintype α).toOuterMeasure event).toReal =
      (Finset.univ.filter (· ∈ event)).card / Fintype.card α := by
  simpa [uniformOfFintype] using
    toOuterMeasure_uniformOfFinset_toReal Finset.univ Finset.univ_nonempty event

/-- The measure of a measurable event under the uniform distribution on a finite type is the
fraction of its members. -/
theorem toMeasure_uniformOfFintype [Fintype α] [Nonempty α] [MeasurableSpace α]
    {event : Set α} [DecidablePred (· ∈ event)] (he : MeasurableSet event) :
    (uniformOfFintype α).toMeasure event =
      (Finset.univ.filter (· ∈ event)).card * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simpa [uniformOfFintype] using
    toMeasure_uniformOfFinset Finset.univ Finset.univ_nonempty he

end Cslib.Probability.PMF
