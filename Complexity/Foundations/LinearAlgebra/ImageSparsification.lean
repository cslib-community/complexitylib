/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Sparsifying images of product maps

Let `π : A → B → X` be a map of finite sets. Suppose a function space `V` on `X` pulls back
to sums of matrices whose columns lie in `U` and matrices whose rows lie in `W`. Then the
image of `π` is covered by the images of a small collection of rows and columns. The number
of selected inputs is at most `dim U + dim W + (|X| - dim V)`.

The proof selects enough coordinates to determine `U` and `W`. A function in `V` supported
on the uncovered outputs must vanish: its pullback vanishes on the selected rows and columns,
which determine every matrix in the slice space. The coordinate space on the uncovered
outputs is therefore disjoint from `V`, bounding the number of exceptions by its codimension.

This is a general linear-algebra argument. The application to Boolean sumsets uses low-degree
polynomial spaces, but neither polynomials nor a group operation appear in this module.

## Main definitions

* `Cslib.ImageSparsification.sliceSpace`: sums of column-constrained and row-constrained matrices.
* `Cslib.ImageSparsification.HasSliceDecomposition`: a product map pulls an output space back
  into a specified slice space.

## Main results

* `Cslib.ImageSparsification.mul_mem_sliceSpace_left`,
  `Cslib.ImageSparsification.mul_mem_sliceSpace_right`: build separable slices from either factor.
* `Cslib.ImageSparsification.hasSliceDecomposition_span`: check the pullback condition
  on generators.
* `Cslib.ImageSparsification.HasSliceDecomposition.comp`: restrict or reparameterize either input.
* `Cslib.ImageSparsification.exists_image_cover_with_exceptions`: separate dimension budgets
  for selected rows, selected columns, and exceptional outputs.
* `Cslib.ImageSparsification.exists_image_cover`: absorb the exceptions to obtain an exact cover.
-/

public section

namespace Cslib.ImageSparsification

open Module Finset

variable {K A B X : Type*} [Field K]

/-- The space of matrices that are sums of a matrix with columns in `U` and a matrix with
rows in `W`. This is the concrete finite-function version of `U ⊗ Kᴮ + Kᴬ ⊗ W`. -/
@[expose] def sliceSpace (U : Submodule K (A → K)) (W : Submodule K (B → K)) :
    Submodule K (A → B → K) where
  carrier := {m | ∃ l r : A → B → K,
    (∀ b, (fun a ↦ l a b) ∈ U) ∧ (∀ a, r a ∈ W) ∧ ∀ a b, m a b = l a b + r a b}
  zero_mem' := ⟨0, 0, fun _ ↦ U.zero_mem, fun _ ↦ W.zero_mem, fun _ _ ↦ (zero_add _).symm⟩
  add_mem' := by
    rintro m n ⟨l, r, hl, hr, hm⟩ ⟨l', r', hl', hr', hn⟩
    refine ⟨l + l', r + r', fun b ↦ U.add_mem (hl b) (hl' b),
      fun a ↦ W.add_mem (hr a) (hr' a), ?_⟩
    intro a b
    change m a b + n a b = (l a b + l' a b) + (r a b + r' a b)
    rw [hm, hn]
    exact add_add_add_comm _ _ _ _
  smul_mem' := by
    rintro c m ⟨l, r, hl, hr, hm⟩
    refine ⟨c • l, c • r, fun b ↦ U.smul_mem c (hl b),
      fun a ↦ W.smul_mem c (hr a), ?_⟩
    intro a b
    change c * m a b = c * l a b + c * r a b
    rw [hm, mul_add]

/-- With zero column and row spaces, the slice space consists only of the zero matrix. -/
@[simp] theorem sliceSpace_bot_bot :
    sliceSpace (⊥ : Submodule K (A → K)) (⊥ : Submodule K (B → K)) = ⊥ := by
  apply le_antisymm
  · rintro m ⟨l, r, hl, hr, heq⟩
    change m = 0
    funext a b
    change m a b = 0
    have hlzero : l a b = 0 := congrFun ((Submodule.mem_bot K).mp (hl b)) a
    have hrzero : r a b = 0 := congrFun ((Submodule.mem_bot K).mp (hr a)) b
    rw [heq, hlzero, hrzero, zero_add]
  · exact bot_le

/-- A separable matrix belongs to the slice space when its left factor belongs to `U`. -/
theorem mul_mem_sliceSpace_left {U : Submodule K (A → K)} (W : Submodule K (B → K))
    {u : A → K} (hu : u ∈ U) (r : B → K) :
    (fun a b ↦ u a * r b) ∈ sliceSpace U W := by
  refine ⟨fun a b ↦ u a * r b, 0, ?_, fun _ ↦ W.zero_mem, fun _ _ ↦ (add_zero _).symm⟩
  intro b
  simpa only [Pi.smul_def, smul_eq_mul, mul_comm] using U.smul_mem (r b) hu

/-- A separable matrix belongs to the slice space when its right factor belongs to `W`. -/
theorem mul_mem_sliceSpace_right (U : Submodule K (A → K)) {W : Submodule K (B → K)}
    (l : A → K) {w : B → K} (hw : w ∈ W) :
    (fun a b ↦ l a * w b) ∈ sliceSpace U W := by
  refine ⟨0, fun a b ↦ l a * w b, fun _ ↦ U.zero_mem, ?_,
    fun _ _ ↦ (zero_add _).symm⟩
  intro a
  exact W.smul_mem (l a) hw

/-- Pulling back every function in `V` along `π` gives a matrix in `sliceSpace U W`. -/
@[expose] def HasSliceDecomposition (π : A → B → X) (U : Submodule K (A → K))
    (W : Submodule K (B → K)) (V : Submodule K (X → K)) : Prop :=
  ∀ v ∈ V, (fun a b ↦ v (π a b)) ∈ sliceSpace U W

/-- It suffices to establish the slice decomposition for generators of the output space. -/
theorem hasSliceDecomposition_span {ι : Type*} (π : A → B → X)
    (U : Submodule K (A → K)) (W : Submodule K (B → K)) (v : ι → X → K)
    (h : ∀ i, (fun a b ↦ v i (π a b)) ∈ sliceSpace U W) :
    HasSliceDecomposition π U W (Submodule.span K (Set.range v)) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨i, rfl⟩ := hf; exact h i
  | zero => exact (sliceSpace U W).zero_mem
  | add f g _ _ hf hg => exact (sliceSpace U W).add_mem hf hg
  | smul c f _ hf => exact (sliceSpace U W).smul_mem c hf

/-- A slice decomposition remains valid after restricting or reparameterizing either input. -/
theorem HasSliceDecomposition.comp {π : A → B → X} {U : Submodule K (A → K)}
    {W : Submodule K (B → K)} {V : Submodule K (X → K)}
    (h : HasSliceDecomposition π U W V) {A' B' : Type*} (f : A' → A) (g : B' → B) :
    HasSliceDecomposition (fun a b ↦ π (f a) (g b))
      (U.map (LinearMap.funLeft K K f)) (W.map (LinearMap.funLeft K K g)) V := by
  intro v hv
  obtain ⟨l, r, hl, hr, heq⟩ := h v hv
  exact ⟨fun a b ↦ l (f a) (g b), fun a b ↦ r (f a) (g b),
    fun b ↦ ⟨fun a ↦ l a (g b), hl (g b), rfl⟩,
    fun a ↦ ⟨r (f a), hr (f a), rfl⟩, fun a b ↦ heq (f a) (g b)⟩

private def evaluation (U : Submodule K (A → K)) (a : A) : Module.Dual K U :=
  (LinearMap.proj a).comp U.subtype

private theorem exists_evaluation_set [Finite A] (U : Submodule K (A → K)) :
    ∃ s : Finset A, s.card ≤ finrank K U ∧
      ∀ a, evaluation U a ∈ Submodule.span K (evaluation U '' (s : Set A)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  obtain ⟨ι, f, hf, hspan, hind⟩ := exists_linearIndependent' K (evaluation U)
  let : Fintype ι := Fintype.ofInjective f hf
  refine ⟨univ.image f, ?_, ?_⟩
  · have hcard : Fintype.card ι ≤ finrank K U := by
      simpa only [Subspace.dual_finrank_eq] using hind.fintype_card_le_finrank
    exact (Finset.card_image_le.trans (by simpa only [card_univ] using hcard))
  · intro a
    have ha : evaluation U a ∈ Submodule.span K (Set.range (evaluation U ∘ f)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨a, rfl⟩
    refine Submodule.span_mono ?_ ha
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, mem_image.mpr ⟨i, mem_univ i, rfl⟩, rfl⟩

private theorem eq_zero_of_mem_sliceSpace {U : Submodule K (A → K)}
    {W : Submodule K (B → K)} {s : Finset A} {t : Finset B}
    (hs : ∀ a, evaluation U a ∈ Submodule.span K (evaluation U '' (s : Set A)))
    (ht : ∀ b, evaluation W b ∈ Submodule.span K (evaluation W '' (t : Set B)))
    {m : A → B → K} (hm : m ∈ sliceSpace U W)
    (hrows : ∀ a ∈ s, ∀ b, m a b = 0) (hcols : ∀ b ∈ t, ∀ a, m a b = 0) :
    m = 0 := by
  obtain ⟨l, r, hl, hr, heq⟩ := hm
  let F : Module.Dual K U →ₗ[K] (B → K) :=
    LinearMap.pi fun b ↦ Module.Dual.eval K U ⟨fun a ↦ l a b, hl b⟩
  have hselected : ∀ a ∈ s, l a ∈ W := by
    intro a ha
    have hlr : l a = -r a := by
      funext b
      exact eq_neg_of_add_eq_zero_left ((heq a b).symm.trans (hrows a ha b))
    rw [hlr]
    exact W.neg_mem (hr a)
  have hspan : Submodule.span K (evaluation U '' (s : Set A)) ≤ W.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact hselected a ha
  have hrowmem (a : A) : m a ∈ W := by
    have hlmem : l a ∈ W := hspan (hs a)
    have hrow : m a = l a + r a := funext (heq a)
    rw [hrow]
    exact W.add_mem hlmem (hr a)
  funext a b
  let G : Module.Dual K W →ₗ[K] K := Module.Dual.eval K W ⟨m a, hrowmem a⟩
  have hspan' : Submodule.span K (evaluation W '' (t : Set B)) ≤ LinearMap.ker G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b', hb', rfl⟩
    exact hcols b' hb' a
  exact hspan' (ht b)

/-- Select at most `dim U` rows and `dim W` columns. Their images cover every output except
for at most `|X| - dim V` outputs, each of which is still in the image of `π`. -/
theorem exists_image_cover_with_exceptions [Finite A] [Finite B] [Fintype X]
    {π : A → B → X} {U : Submodule K (A → K)} {W : Submodule K (B → K)}
    {V : Submodule K (X → K)} (h : HasSliceDecomposition π U W V) :
    ∃ (s : Finset A) (t : Finset B) (e : Finset X),
      s.card ≤ finrank K U ∧ t.card ≤ finrank K W ∧
      e.card ≤ Fintype.card X - finrank K V ∧
      (∀ x ∈ e, ∃ a b, π a b = x) ∧
      ∀ a b, π a b ∈ e ∨ (∃ a' ∈ s, ∃ b', π a' b' = π a b) ∨
        (∃ b' ∈ t, ∃ a', π a' b' = π a b) := by
  classical
  obtain ⟨s, hscard, hs⟩ := exists_evaluation_set U
  obtain ⟨t, htcard, ht⟩ := exists_evaluation_set W
  let e := univ.filter fun x ↦ (∃ a b, π a b = x) ∧
    ¬(∃ a ∈ s, ∃ b, π a b = x) ∧ ¬(∃ b ∈ t, ∃ a, π a b = x)
  have hdisjoint : Disjoint V (Pi.spanSubset K (e : Set X)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv he
    have hout : ∀ x ∉ e, v x = 0 := Pi.mem_spanSubset_iff.mp he
    have hpull : (fun a b ↦ v (π a b)) = 0 := by
      apply eq_zero_of_mem_sliceSpace hs ht (h v hv)
      · intro a ha b
        apply hout
        intro hx
        exact (mem_filter.mp hx).2.2.1 ⟨a, ha, b, rfl⟩
      · intro b hb a
        apply hout
        intro hx
        exact (mem_filter.mp hx).2.2.2 ⟨b, hb, a, rfl⟩
    funext x
    by_cases hx : x ∈ e
    · obtain ⟨a, b, rfl⟩ := (mem_filter.mp hx).2.1
      exact congrFun (congrFun hpull a) b
    · exact hout x hx
  have hecard : e.card ≤ Fintype.card X - finrank K V := by
    have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
    rw [Pi.dim_spanSubset, Set.ncard_coe_finset, Module.finrank_fintype_fun_eq_card] at hdim
    omega
  refine ⟨s, t, e, hscard, htcard, hecard, ?_, ?_⟩
  · intro x hx
    exact (mem_filter.mp hx).2.1
  · intro a b
    by_cases hleft : ∃ a' ∈ s, ∃ b', π a' b' = π a b
    · exact Or.inr (Or.inl hleft)
    by_cases hright : ∃ b' ∈ t, ∃ a', π a' b' = π a b
    · exact Or.inr (Or.inr hright)
    exact Or.inl (mem_filter.mpr ⟨mem_univ _, ⟨a, b, rfl⟩, hleft, hright⟩)

/-- **Image sparsification.** If the output function space pulls back into a two-sided slice
space, the image is covered by rows and columns with total budget
`dim U + dim W + (|X| - dim V)`. All selected coordinates are actual inputs of `π`.

The construction is nonuniform: each exceptional output is absorbed by choosing one of its
preimages. No algorithm for finding the selected coordinates is asserted. -/
theorem exists_image_cover [Finite A] [Finite B] [Fintype X]
    {π : A → B → X} {U : Submodule K (A → K)} {W : Submodule K (B → K)}
    {V : Submodule K (X → K)} (h : HasSliceDecomposition π U W V) :
    ∃ (s : Finset A) (t : Finset B),
      s.card + t.card ≤ finrank K U + finrank K W + (Fintype.card X - finrank K V) ∧
      ∀ a b, (∃ a' ∈ s, ∃ b', π a' b' = π a b) ∨
        (∃ b' ∈ t, ∃ a', π a' b' = π a b) := by
  classical
  obtain ⟨s, t, e, hscard, htcard, hecard, heimage, hcover⟩ :=
    exists_image_cover_with_exceptions h
  have hex : ∀ x : e, ∃ a b, π a b = x := fun x ↦ heimage x x.property
  choose a b hab using hex
  refine ⟨s ∪ univ.image a, t, ?_, ?_⟩
  · have hcard : (s ∪ univ.image a).card ≤ s.card + e.card := by
      calc
        (s ∪ univ.image a).card ≤ s.card + (univ.image a).card := card_union_le _ _
        _ ≤ s.card + e.card := Nat.add_le_add_left (by
          simpa only [card_univ, Fintype.card_coe] using card_image_le (f := a) (s := univ)) _
    omega
  · intro a₀ b₀
    rcases hcover a₀ b₀ with he | hleft | hright
    · exact Or.inl ⟨a ⟨π a₀ b₀, he⟩,
        mem_union_right _ (mem_image.mpr ⟨⟨π a₀ b₀, he⟩, mem_univ _, rfl⟩),
        b ⟨π a₀ b₀, he⟩, hab ⟨π a₀ b₀, he⟩⟩
    · obtain ⟨a', ha', b', hab'⟩ := hleft
      exact Or.inl ⟨a', mem_union_left _ ha', b', hab'⟩
    · exact Or.inr hright

end Cslib.ImageSparsification
