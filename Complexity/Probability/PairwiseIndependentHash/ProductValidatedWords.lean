/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Power
public import Complexity.Probability.PairwiseIndependentHash.ComponentGap
public import Complexity.Probability.PairwiseIndependentHash.ValidatedWords
import Complexity.Foundations.Data.Finset.Expect

/-!
# Validated walk words for the multi-component product sampler

`Complexity.Probability.PairwiseIndependentHash.ValidatedWords` expresses `t` steps of the lazy
conditional walk on a single retention slice as an iterate of a validated variant operator over the
ambient channel space `FrameChannel P H r`. Meanwhile,
`Complexity.Probability.PairwiseIndependentHash.ComponentGap` proves the spectral gap for the
multi-component lazy product walk (`componentMove H M P L`, transported along `componentEquiv`) over
`J` conditioned channels together with a free-bit torus `(ZMod M) ^ H`.

This module bridges those two layers by formalizing Section 6.1, Lemma 6.3 (`lem:env-variants`,
items 1–4) of [OpenAI2026LogSpace] directly on the multi-component product environment
`ComponentSpace H M P = (∀ j, FrameChannel (P j) H 1) × (Fin H → ZMod M)`:

* **Bounded-alphabet description (`O(t)` symbols, Lemma 6.3 preamble).** Each step label in
  `ComponentLazyStep H J` has `4 (J + 1) H ^ 2` choices (`card_componentLazyStep`), and each
  candidate wrap vector lies in `affineWrapBox H = {-3, …, 3} ^ H` of cardinality `7 ^ H`
  (`card_affineWrapBox`), independently of the primes `P j`, the side lengths `L j`, the torus
  modulus `M`, the retained identifiers `y j`, and the walk length `t`.
* **Bijectivity, measure invariance, and identifier independence (items 1–2).** Every step
  `componentStepPerm L e z` and every length-`t` word `componentWordPerm L w z` is an
  `Equiv.Perm (ComponentSpace H M P)` preserving uniform expectations (`expect_componentWordPerm`)
  and depending only on `L`, `w`, and `z`—never on the retained identifiers `y`.
* **Unique valid wrap word along the slice trajectory (item 3).** Initial slice membership is
  carried by `ComponentSlice H M P L y`, and the identifier `y j` enters the step test only through
  `IsValidComponentStep` on `(A.1 j).eval (y j)` (while torus steps and lazy self-loops require
  `z = 0`). For every `A` in `ComponentSlice H M P L y` and every move word `w` of length `t`,
  there is a unique wrap word `z` passing `IsValidComponentWord`
  (`existsUnique_isValidComponentWord`), it lies in `(affineWrapBox H) ^ t`
  (`componentWordWrap_mem`), and `componentWordPerm L w z` maps `A` to the exact endpoint
  `(G.pow t).neighbor A w` of the walk along `w` in the reindexed lazy product multigraph `G`
  (`componentWordPerm_wrap_eq`, using `RotationMap.pow`).
* **Exact conditional walk identity (item 4).** Averaging over `w : Fin t → ComponentLazyStep H J`
  and summing over `z ∈ (affineWrapBox H) ^ t`—with no normalization by `(7 ^ H) ^ t`—recovers the
  exact `t`-step lazy product walk on `ComponentSlice H M P L y`
  (`walk_pow_componentMove_eq_iterate`, `walk_pow_componentMove_eq_expect_word`).

## Main definitions

* `Cslib.Probability.affineWrapBox`: the candidate wrap box `{-3, …, 3} ^ H`.
* `Cslib.Probability.ComponentMoveIndex`, `Cslib.Probability.ComponentLazyStep`: generator and
  lazy-edge alphabets of the multi-component product walk.
* `Cslib.Probability.ComponentSpace`, `Cslib.Probability.ComponentSlice`,
  `Cslib.Probability.componentSliceVal`: the ambient multi-component space, the product retention
  slice for `y`, and its forgetful embedding.
* `Cslib.Probability.componentStepPerm`, `Cslib.Probability.componentWordPerm`: identifier-free
  ambient permutations for one step and for length-`t` words.
* `Cslib.Probability.IsValidComponentStep`, `Cslib.Probability.IsValidComponentWord`: endpoint wrap
  predicates for one step and for length-`t` words.
* `Cslib.Probability.componentStepWrap`, `Cslib.Probability.componentWordWrap`: the unique valid
  wrap vector and length-`t` wrap word.
* `Cslib.Probability.componentValidatedStep`: one-step validated walk operator on `ComponentSpace`.

## Main results

* `Cslib.Probability.card_affineWrapBox`, `Cslib.Probability.card_componentLazyStep`: explicit
  alphabet cardinalities `7 ^ H` and `4 * (J + 1) * H ^ 2`.
* `Cslib.Probability.expect_componentWordPerm`: uniform-expectation invariance of every word
  permutation on `ComponentSpace H M P`.
* `Cslib.Probability.existsUnique_isValidComponentWord`,
  `Cslib.Probability.componentWordWrap_mem`, `Cslib.Probability.componentWordPerm_wrap_eq`: unique
  valid wrap word in `(affineWrapBox H) ^ t`, reaching the walk endpoint `(G.pow t).neighbor A w`.
* `Cslib.Probability.walk_pow_componentMove_eq_iterate`,
  `Cslib.Probability.walk_pow_componentMove_eq_expect_word`: `t` steps of the lazy product walk on
  `ComponentSlice H M P L y` equal both the `t`-fold iterate of `componentValidatedStep` and the
  explicit expectation-and-sum over length-`t` validated words.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 6.1, Lemma 6.3 (`lem:env-variants`), items 1–4.
-/

public section

namespace Cslib.Probability

open Finset Function RotationMap
open scoped BigOperators

/-! ### Bounded alphabets and ambient multi-component space -/

/-- The candidate wrap box `{-3, …, 3} ^ H`, independent of the primes, side lengths, torus
modulus, identifiers, and walk length. -/
@[expose] def affineWrapBox (H : ℕ) : Finset (Fin H → ℤ) :=
  Fintype.piFinset fun _ ↦ Icc (-3 : ℤ) 3

/-- The wrap box `affineWrapBox H` has cardinality `7 ^ H`. -/
theorem card_affineWrapBox (H : ℕ) : #(affineWrapBox H) = 7 ^ H := by
  have h7 : #(Icc (-3 : ℤ) 3) = 7 := by decide
  rw [affineWrapBox, Fintype.piFinset, card_map, card_pi, prod_const, card_univ,
    Fintype.card_fin, h7]

private theorem zero_mem_affineWrapBox (H : ℕ) : (0 : Fin H → ℤ) ∈ affineWrapBox H := by
  rw [affineWrapBox, Fintype.mem_piFinset]
  intro _
  rw [Pi.zero_apply, mem_Icc]
  omega

/-- Generator index of `componentMove H M P L`: either a channel index `j : Fin J` paired with an
affine generator, or a torus affine generator. -/
abbrev ComponentMoveIndex (H J : ℕ) : Type :=
  (Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
    ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H)

/-- Edge label of the lazy product walk `(ofPerms (componentMove H M P L)).lazy`: `.inl (m, b)`
applies generator `m` in direction `b`, while `.inr (m, b)` is a lazy self-loop. -/
abbrev ComponentLazyStep (H J : ℕ) : Type :=
  (ComponentMoveIndex H J × Bool) ⊕ (ComponentMoveIndex H J × Bool)

/-- The lazy product walk has `4 * (J + 1) * H ^ 2` edge labels per step. -/
theorem card_componentLazyStep (H J : ℕ) :
    Fintype.card (ComponentLazyStep H J) = 4 * (J + 1) * H ^ 2 := by
  rw [Fintype.card_sum, Fintype.card_prod, card_componentMove_index, Fintype.card_bool]
  ring

/-- The ambient multi-component environment: `J` frame channels of rank `1` together with a
free-bit torus `(ZMod M) ^ H`. -/
abbrev ComponentSpace (H M : ℕ) {J : ℕ} (P : Fin J → ℕ) : Type :=
  (∀ j, FrameChannel (P j) H 1) × (Fin H → ZMod M)

/-- The product retention slice retaining `y j` in channel `j` for all `j : Fin J`, paired with
the free-bit torus `(ZMod M) ^ H`. -/
abbrev ComponentSlice (H M : ℕ) {J : ℕ} (P : Fin J → ℕ) [∀ j, NeZero (P j)]
    (L : Fin J → ℕ) (y : ∀ j, ZMod (P j)) : Type :=
  (∀ j, RetentionSlice (P j) H 1 (L j) (y j)) × (Fin H → ZMod M)

/-- Forgetful embedding from the product retention slice into the ambient `ComponentSpace`. -/
@[expose] def componentSliceVal {H M J : ℕ} {P : Fin J → ℕ} [∀ j, NeZero (P j)]
    {L : Fin J → ℕ} {y : ∀ j, ZMod (P j)}
    (A : ComponentSlice H M P L y) : ComponentSpace H M P :=
  Prod.map (fun S j ↦ (S j).val) id A

/-! ### One-step ambient variant permutations and wrap validation -/

section OneStep

variable {H M J : ℕ} {P : Fin J → ℕ}

/-- **One-step ambient variant permutation** (Lemma 6.3, items 1–2, for `t = 1`).
* On `.inr _` (a lazy self-loop), it is the identity permutation.
* On `.inl (.inr k, b)` (a torus move), it applies `torusMove H M k` (or its inverse when
  `b = true`) to the torus coordinate.
* On `.inl (.inl ⟨j, k⟩, b)` (a move on channel `j`), it applies `variantMove (L j)` with wrap
  vector `z` to channel `j` and leaves all other components unchanged.

Crucially, this permutation of `ComponentSpace H M P` does not depend on the identifiers `y`. -/
@[expose] def componentStepPerm (L : Fin J → ℕ)
    (e : ComponentLazyStep H J) (z : Fin H → ℤ) : Equiv.Perm (ComponentSpace H M P) :=
  match e with
  | .inr _ => Equiv.refl _
  | .inl (.inr k, b) =>
    (Equiv.refl _).prodCongr (bif b then (torusMove H M k).symm else torusMove H M k)
  | .inl (.inl ⟨j, k⟩, b) =>
    let mv := signedMove (affineGenerator H k) b
    (Equiv.piCongrRight (update (fun _ ↦ Equiv.refl _) j
      (variantMove (L j) mv.1 mv.2 z))).prodCongr (Equiv.refl _)

/-- **One-step wrap validation test** on `ComponentSpace H M P`. Initial slice membership is carried
by `ComponentSlice H M P L y` (matching `ConditionalAveraging` and `ValidatedWords`); channel moves
test `IsValidWrap` on `(A.1 j).eval (y j)` alone, while torus moves and lazy self-loops require
`z = 0`. -/
@[expose] def IsValidComponentStep (L : Fin J → ℕ) (y : ∀ j, ZMod (P j))
    (e : ComponentLazyStep H J) (z : Fin H → ℤ) (A : ComponentSpace H M P) : Prop :=
  match e with
  | .inr _ => z = 0
  | .inl (.inr _, _) => z = 0
  | .inl (.inl ⟨j, k⟩, b) =>
    let mv := signedMove (affineGenerator H k) b
    IsValidWrap (L j) mv.1 mv.2 z ((A.1 j).eval (y j))

instance instDecidableIsValidComponentStep (L : Fin J → ℕ) (y : ∀ j, ZMod (P j))
    (e : ComponentLazyStep H J) (z : Fin H → ℤ) (A : ComponentSpace H M P) :
    Decidable (IsValidComponentStep L y e z A) :=
  match e with
  | .inr _ => inferInstanceAs (Decidable (z = 0))
  | .inl (.inr _, _) => inferInstanceAs (Decidable (z = 0))
  | .inl (.inl ⟨j, k⟩, b) =>
    inferInstanceAs (Decidable (IsValidWrap (L j) (signedMove (affineGenerator H k) b).1
      (signedMove (affineGenerator H k) b).2 z ((A.1 j).eval (y j))))

/-- The unique wrap vector passing `IsValidComponentStep L y e · A`. -/
@[expose] def componentStepWrap (L : Fin J → ℕ) (y : ∀ j, ZMod (P j))
    (e : ComponentLazyStep H J) (A : ComponentSpace H M P) : Fin H → ℤ :=
  match e with
  | .inr _ => 0
  | .inl (.inr _, _) => 0
  | .inl (.inl ⟨j, k⟩, b) =>
    let mv := signedMove (affineGenerator H k) b
    wrap (L j) mv.1 mv.2 ((A.1 j).eval (y j))

theorem isValidComponentStep_iff {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    {y : ∀ j, ZMod (P j)} {e : ComponentLazyStep H J} {z : Fin H → ℤ}
    {A : ComponentSpace H M P} :
    IsValidComponentStep L y e z A ↔ z = componentStepWrap L y e A := by
  rcases e with ⟨⟨j, k⟩ | k, b⟩ | d
  · exact isValidWrap_iff
  · rfl
  · rfl

theorem componentStepWrap_mem [∀ j, NeZero (P j)] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    {y : ∀ j, ZMod (P j)} (e : ComponentLazyStep H J) (A : ComponentSlice H M P L y) :
    componentStepWrap L y e (componentSliceVal A) ∈ affineWrapBox H := by
  rcases e with ⟨⟨j, k⟩ | k, b⟩ | d
  · exact wrap_affineGenerator_mem k b (A.1 j).2
  · exact zero_mem_affineWrapBox H
  · exact zero_mem_affineWrapBox H

/-- On the product retention slice, the ambient variant with `componentStepWrap` coincides with the
exact neighbor in the reindexed lazy product multigraph. -/
theorem componentStepPerm_wrap_eq [∀ j, Fact (P j).Prime] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)} (e : ComponentLazyStep H J)
    (A : ComponentSlice H M P L y) :
    componentStepPerm L e (componentStepWrap L y e (componentSliceVal A)) (componentSliceVal A) =
      componentSliceVal
        (((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).neighbor
          A e) := by
  rcases e with ⟨⟨j, k⟩ | k, b⟩ | d
  · refine Prod.ext (funext fun j' ↦ ?_) ?_
    · by_cases hj : j' = j
      · subst hj
        cases b
        · simpa only [componentStepPerm, componentStepWrap, componentSliceVal, signedMove,
            Bool.cond_false, neighbor_reindex, Equiv.symm_symm, neighbor_lazy_inl,
            neighbor_ofPerms_false, componentMove, boxProdPerms, Sum.elim_inl, componentEquiv,
            Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_fst, piPerms,
            Equiv.piCongrRight_symm_apply, Equiv.piCongrRight_apply, Pi.map_apply, update_self,
            affineMove] using
            variantMove_wrap_eq (hL j') (affineGenerator H k).1 (affineGenerator H k).2 (A.1 j')
        · simpa only [componentStepPerm, componentStepWrap, componentSliceVal, signedMove,
            Bool.cond_true, neighbor_reindex, Equiv.symm_symm, neighbor_lazy_inl,
            neighbor_ofPerms_true, componentMove, boxProdPerms, Sum.elim_inl, componentEquiv,
            Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_fst, piPerms,
            Equiv.piCongrRight_symm_apply, Equiv.piCongrRight_apply, Pi.map_apply, update_self,
            affineMove, coordMove_symm] using
            variantMove_wrap_eq (hL j') (signedMove (affineGenerator H k) true).1
              (signedMove (affineGenerator H k) true).2 (A.1 j')
      · cases b <;>
          simp only [componentStepPerm, componentSliceVal, neighbor_reindex, Equiv.symm_symm,
            neighbor_lazy_inl, neighbor_ofPerms_false, neighbor_ofPerms_true, componentMove,
            boxProdPerms, Sum.elim_inl, componentEquiv, Equiv.prodCongr_symm, Equiv.refl_symm,
            Equiv.prodCongr_apply, Prod.map_fst, piPerms, Equiv.piCongrRight_symm_apply,
            Equiv.piCongrRight_apply, Pi.map_apply, update_of_ne hj, Equiv.refl_apply,
            Equiv.symm_apply_apply]
    · cases b <;>
        simp only [componentStepPerm, componentSliceVal, neighbor_reindex, Equiv.symm_symm,
          neighbor_lazy_inl, neighbor_ofPerms_false, neighbor_ofPerms_true, componentMove,
          boxProdPerms, Sum.elim_inl, componentEquiv, Equiv.prodCongr_symm, Equiv.refl_symm,
          Equiv.prodCongr_apply, Prod.map_snd, Equiv.refl_apply]
  · refine Prod.ext (funext fun j' ↦ ?_) ?_
    · cases b <;>
        simp only [componentStepPerm, componentSliceVal, Bool.cond_false, Bool.cond_true,
          neighbor_reindex, Equiv.symm_symm, neighbor_lazy_inl, neighbor_ofPerms_false,
          neighbor_ofPerms_true, componentMove, boxProdPerms, Sum.elim_inr, componentEquiv,
          Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_fst,
          Equiv.refl_apply, Equiv.symm_apply_apply]
    · cases b <;>
        simp only [componentStepPerm, componentSliceVal, Bool.cond_false, Bool.cond_true,
          neighbor_reindex, Equiv.symm_symm, neighbor_lazy_inl, neighbor_ofPerms_false,
          neighbor_ofPerms_true, componentMove, boxProdPerms, Sum.elim_inr, componentEquiv,
          Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_snd,
          Equiv.refl_apply, id_eq]
  · rw [neighbor_reindex, Equiv.symm_symm, neighbor_lazy_inr, Equiv.symm_apply_apply]
    rfl

/-- **One-step sum over candidate wraps**: summing `f` over `z ∈ affineWrapBox H` filtered by
`IsValidComponentStep` gives `f` at the conditional slice neighbor. -/
theorem sum_ite_isValidComponentStep [∀ j, Fact (P j).Prime] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)} {R : Type*} [AddCommMonoid R]
    (e : ComponentLazyStep H J) (f : ComponentSpace H M P → R) (A : ComponentSlice H M P L y) :
    ∑ z ∈ affineWrapBox H,
        (if IsValidComponentStep L y e z (componentSliceVal A)
          then f (componentStepPerm L e z (componentSliceVal A)) else 0) =
      f (componentSliceVal
        (((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).neighbor
          A e)) := by
  simp only [isValidComponentStep_iff, sum_ite_eq', componentStepWrap_mem, ite_true,
    componentStepPerm_wrap_eq hL]

/-- **One-step validated operator on `ComponentSpace H M P`**. -/
@[expose] noncomputable def componentValidatedStep (L : Fin J → ℕ)
    (y : ∀ j, ZMod (P j)) (g : ComponentSpace H M P → ℝ) (A : ComponentSpace H M P) : ℝ :=
  𝔼 e : ComponentLazyStep H J, ∑ z ∈ affineWrapBox H,
    if IsValidComponentStep L y e z A then g (componentStepPerm L e z A) else 0

/-- **Iterated validated operator computes the lazy product walk** on `ComponentSlice H M P L y`. -/
theorem walk_pow_componentMove_eq_iterate [∀ j, Fact (P j).Prime] {L : Fin J → ℕ}
    [∀ j, NeZero (L j)] (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)}
    (f : ComponentSpace H M P → ℝ) (t : ℕ) (A : ComponentSlice H M P L y) :
    ((((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).walk ^ t)
        (fun B ↦ f (componentSliceVal B)) A) =
      (componentValidatedStep L y)^[t] f (componentSliceVal A) := by
  set G := (ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm
  induction t generalizing A with
  | zero => rfl
  | succ t ih =>
    have hfun : (G.walk ^ t) (fun B ↦ f (componentSliceVal B)) =
        fun B ↦ (componentValidatedStep L y)^[t] f (componentSliceVal B) := funext ih
    rw [pow_succ', Module.End.mul_apply, hfun, Function.iterate_succ_apply',
      RotationMap.walk_apply, componentValidatedStep]
    exact expect_congr rfl fun e _ ↦
      (sum_ite_isValidComponentStep hL e ((componentValidatedStep L y)^[t] f) A).symm

end OneStep

/-! ### Explicit length-`t` validated walk words (Lemma 6.3, items 1–4) -/

section Words

variable {H M J : ℕ} {P : Fin J → ℕ}

/-- **Ambient permutation of a length-`t` word** `(w, z)` (Lemma 6.3, items 1–2): applies step `0`,
then step `1`, …, through step `t - 1`. Because it is a composition of `Equiv.Perm`s, it is
automatically a bijection of `ComponentSpace H M P` independent of the identifiers `y`. -/
@[expose] def componentWordPerm (L : Fin J → ℕ) :
    ∀ {t : ℕ}, (Fin t → ComponentLazyStep H J) → (Fin t → Fin H → ℤ) →
      Equiv.Perm (ComponentSpace H M P)
  | 0, _, _ => Equiv.refl _
  | _ + 1, w, z =>
    (componentStepPerm L (w 0) (z 0)).trans
      (componentWordPerm L (w ∘ Fin.succ) (z ∘ Fin.succ))

/-- **Uniform-measure invariance** (Lemma 6.3, item 1): every word permutation preserves uniform
expectations on `ComponentSpace H M P`. -/
theorem expect_componentWordPerm [∀ j, NeZero (P j)] [NeZero M] (L : Fin J → ℕ) {t : ℕ}
    (w : Fin t → ComponentLazyStep H J) (z : Fin t → Fin H → ℤ)
    {R : Type*} [AddCommMonoid R] [Module ℚ≥0 R] (g : ComponentSpace H M P → R) :
    𝔼 A, g (componentWordPerm L w z A) = 𝔼 A, g A :=
  Fintype.expect_equiv (componentWordPerm L w z) _ _ fun _ ↦ rfl

/-- **Sequential wrap validation along a length-`t` word**: each step's wrap vector must pass
`IsValidComponentStep` at the intermediate ambient state reached by the preceding prefix. -/
@[expose] def IsValidComponentWord (L : Fin J → ℕ) (y : ∀ j, ZMod (P j)) :
    ∀ {t : ℕ}, (Fin t → ComponentLazyStep H J) → (Fin t → Fin H → ℤ) →
      ComponentSpace H M P → Prop
  | 0, _, _, _ => True
  | _ + 1, w, z, A =>
    IsValidComponentStep L y (w 0) (z 0) A ∧
      IsValidComponentWord L y (w ∘ Fin.succ) (z ∘ Fin.succ)
        (componentStepPerm L (w 0) (z 0) A)

instance instDecidableIsValidComponentWord (L : Fin J → ℕ)
    (y : ∀ j, ZMod (P j)) :
    ∀ {t : ℕ} (w : Fin t → ComponentLazyStep H J) (z : Fin t → Fin H → ℤ)
      (A : ComponentSpace H M P), Decidable (IsValidComponentWord L y w z A)
  | 0, _, _, _ => instDecidableTrue
  | _ + 1, w, z, A =>
    @instDecidableAnd _ _ (instDecidableIsValidComponentStep L y (w 0) (z 0) A)
      (instDecidableIsValidComponentWord L y (w ∘ Fin.succ) (z ∘ Fin.succ)
        (componentStepPerm L (w 0) (z 0) A))

/-- The unique valid wrap word of length `t` for move word `w` starting at ambient state `A`. -/
@[expose] def componentWordWrap (L : Fin J → ℕ) (y : ∀ j, ZMod (P j)) :
    ∀ {t : ℕ}, (Fin t → ComponentLazyStep H J) → ComponentSpace H M P → Fin t → Fin H → ℤ
  | 0, _, _ => Fin.elim0
  | _ + 1, w, A =>
    let z₀ := componentStepWrap L y (w 0) A
    Fin.cons z₀ (componentWordWrap L y (w ∘ Fin.succ) (componentStepPerm L (w 0) z₀ A))

theorem isValidComponentWord_iff {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    {y : ∀ j, ZMod (P j)} :
    ∀ {t : ℕ} {w : Fin t → ComponentLazyStep H J} {z : Fin t → Fin H → ℤ}
      {A : ComponentSpace H M P},
      IsValidComponentWord L y w z A ↔ z = componentWordWrap L y w A
  | 0, _, z, _ => ⟨fun _ ↦ Subsingleton.elim z Fin.elim0, fun _ ↦ trivial⟩
  | _ + 1, w, z, A => by
    simp only [IsValidComponentWord, isValidComponentStep_iff, componentWordWrap]
    constructor
    · rintro ⟨hz₀, htail⟩
      rw [hz₀] at htail
      have htail' := isValidComponentWord_iff.1 htail
      funext i
      exact Fin.cases (by simpa using hz₀) (fun j ↦ congrFun htail' j) i
    · intro hz
      have hz₀ : z 0 = componentStepWrap L y (w 0) A := by
        simpa using congrFun hz 0
      refine ⟨hz₀, ?_⟩
      rw [hz₀, isValidComponentWord_iff]
      funext j
      simpa using congrFun hz j.succ

/-- **Existence and uniqueness of the valid wrap word** (Lemma 6.3, item 3): for every ambient
state `A` and every move word `w`, exactly one wrap word `z` passes `IsValidComponentWord`. -/
theorem existsUnique_isValidComponentWord {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (y : ∀ j, ZMod (P j)) {t : ℕ} (w : Fin t → ComponentLazyStep H J)
    (A : ComponentSpace H M P) :
    ∃! z : Fin t → Fin H → ℤ, IsValidComponentWord L y w z A :=
  ⟨componentWordWrap L y w A, isValidComponentWord_iff.2 rfl, fun _ hz ↦
    isValidComponentWord_iff.1 hz⟩

/-- On `ComponentSlice H M P L y`, the unique valid wrap word lies in `(affineWrapBox H) ^ t`
(Lemma 6.3, bounded-alphabet preamble and item 3). -/
theorem componentWordWrap_mem [∀ j, Fact (P j).Prime] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)} :
    ∀ {t : ℕ} (w : Fin t → ComponentLazyStep H J) (A : ComponentSlice H M P L y),
      componentWordWrap L y w (componentSliceVal A) ∈
        Fintype.piFinset fun _ : Fin t ↦ affineWrapBox H
  | 0, _, _ => by
    rw [Fintype.mem_piFinset]
    exact fun a ↦ a.elim0
  | _ + 1, w, A => by
    rw [Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [componentWordWrap] using componentStepWrap_mem (w 0) A
    · simp only [componentWordWrap, Fin.cons_succ, componentStepPerm_wrap_eq hL]
      have hmem := componentWordWrap_mem hL (w ∘ Fin.succ)
        (((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).neighbor
          A (w 0))
      exact (Fintype.mem_piFinset.1 hmem) j

/-- On `ComponentSlice H M P L y`, applying `componentWordPerm` with the unique valid wrap word
reaches the endpoint `(G.pow t).neighbor A w` of the walk along `w` in the reindexed lazy product
multigraph `G` (Lemma 6.3, item 3). -/
theorem componentWordPerm_wrap_eq [∀ j, Fact (P j).Prime] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)} :
    ∀ {t : ℕ} (w : Fin t → ComponentLazyStep H J) (A : ComponentSlice H M P L y),
      componentWordPerm L w (componentWordWrap L y w (componentSliceVal A))
          (componentSliceVal A) =
        componentSliceVal
          ((((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).pow
            t).neighbor A w)
  | 0, _, _ => rfl
  | _ + 1, w, A => by
    simp only [componentWordPerm, componentWordWrap, Equiv.trans_apply, Fin.cons_zero,
      neighbor_pow_succ]
    have hcons :
        (Fin.cons (componentStepWrap L y (w 0) (componentSliceVal A))
          (componentWordWrap L y (w ∘ Fin.succ)
            (componentStepPerm L (w 0) (componentStepWrap L y (w 0) (componentSliceVal A))
              (componentSliceVal A)))) ∘ Fin.succ =
        componentWordWrap L y (w ∘ Fin.succ)
          (componentStepPerm L (w 0) (componentStepWrap L y (w 0) (componentSliceVal A))
            (componentSliceVal A)) :=
      funext fun _ ↦ rfl
    rw [hcons, componentStepPerm_wrap_eq hL]
    exact componentWordPerm_wrap_eq hL (w ∘ Fin.succ) _

/-- **Exactly one length-`t` wrap word survives** on `ComponentSlice H M P L y`, evaluating to the
endpoint `(G.pow t).neighbor A w` of the walk along `w` in the reindexed lazy product multigraph
`G`. -/
theorem sum_ite_isValidComponentWord [∀ j, Fact (P j).Prime] {L : Fin J → ℕ} [∀ j, NeZero (L j)]
    (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)} {R : Type*} [AddCommMonoid R]
    {t : ℕ} (w : Fin t → ComponentLazyStep H J) (f : ComponentSpace H M P → R)
    (A : ComponentSlice H M P L y) :
    ∑ z ∈ Fintype.piFinset (fun _ : Fin t ↦ affineWrapBox H),
        (if IsValidComponentWord L y w z (componentSliceVal A)
          then f (componentWordPerm L w z (componentSliceVal A)) else 0) =
      f (componentSliceVal
        ((((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).pow
          t).neighbor A w)) := by
  simp only [isValidComponentWord_iff, sum_ite_eq', componentWordWrap_mem hL, ite_true,
    componentWordPerm_wrap_eq hL]

/-- **Length-`t` validated words compute the lazy multi-component conditional walk**
(Lemma 6.3, item 4). Averaging over move words `w : Fin t → ComponentLazyStep H J` and summing over
wrap words `z ∈ (affineWrapBox H) ^ t`—without dividing by `#(affineWrapBox H) ^ t`—equals `t`
steps of the lazy product walk on `ComponentSlice H M P L y`. -/
theorem walk_pow_componentMove_eq_expect_word [∀ j, Fact (P j).Prime] {L : Fin J → ℕ}
    [∀ j, NeZero (L j)] (hL : ∀ j, L j ≤ P j) {y : ∀ j, ZMod (P j)}
    (f : ComponentSpace H M P → ℝ) (t : ℕ) (A : ComponentSlice H M P L y) :
    ((((ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm).walk ^ t)
        (fun B ↦ f (componentSliceVal B)) A) =
      𝔼 w : Fin t → ComponentLazyStep H J,
        ∑ z ∈ Fintype.piFinset (fun _ : Fin t ↦ affineWrapBox H),
          if IsValidComponentWord L y w z (componentSliceVal A)
          then f (componentWordPerm L w z (componentSliceVal A)) else 0 := by
  rw [← walk_pow, walk_apply]
  exact expect_congr rfl fun w _ ↦ (sum_ite_isValidComponentWord hL w f A).symm

end Words

end Cslib.Probability
