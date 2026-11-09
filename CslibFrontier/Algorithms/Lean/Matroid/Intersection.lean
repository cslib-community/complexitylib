/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Matroid intersection: min–max theorem and augmenting paths

For matroids `M₁ M₂ : Matroid α` and a finite candidate ground set `E : Finset α`, this module
proves **Edmonds' matroid intersection theorem**: the maximum cardinality of a common independent
subset of `E` equals the minimum over `U ⊆ E` of `M₁.eRk U + M₂.eRk (E \ U)`. The proof is
algorithmic and follows [Schrijver2017], Section 10.5. It defines the exchange digraph
`H(M₁, M₂, I)` of a common independent set `I`, shows that augmenting `I` along a shortest
source-to-sink walk gives a common independent set with one more element (Theorem 10.6), and shows
that if no such walk exists then the set of vertices unreachable from the sources certifies that
`I` is maximum (Theorem 10.7). Iterating the two cases gives the min–max equality (Theorem 10.9).

The matroids need not have ground set `E`: elements of `E` outside `Mᵢ.E` behave as loops of `Mᵢ`
(they lie in no independent set), and `eRk` only depends on the part of a set inside the ground
set. Taking `E` to be the common finite
ground set recovers [Schrijver2017], Theorem 10.9 verbatim (`iSup_encard_eq_iInf_eRk_add_eRk`).

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.IsCommonIndep`, `IsMaxCommonIndep`: common independent sets of
  two matroids and maximum-cardinality common independent subsets of `E`.
* `Cslib.Algorithms.Lean.Matroid.IsExchSource`, `IsExchSink`: the source set `X₁(I)` and sink set
  `X₂(I)` of the exchange digraph.
* `Cslib.Algorithms.Lean.Matroid.IsExchArc`, `IsExchWalk`, `IsExchAugWalk`,
  `IsShortestExchAugWalk`: arcs and walks of the exchange digraph `H(M₁, M₂, I)` on `E`, and
  (shortest) walks from `X₁(I)` to `X₂(I)`.

## Main results

* `Cslib.Algorithms.Lean.Matroid.encard_le_eRk_add_eRk`,
  `Cslib.Algorithms.Lean.Matroid.IsCommonIndep.card_le_eRk_add_eRk`,
  `Cslib.Algorithms.Lean.Matroid.IsCommonIndep.card_le_rk_add_rk`: weak duality.
* `Cslib.Algorithms.Lean.Matroid.indep_exchange_chain`: exchanging along a chordless
  ("triangular") exchange sequence preserves independence, the case of [Schrijver2017], Lemma 10.2
  used by the augmenting-path step.
* `Cslib.Algorithms.Lean.Matroid.card_eq_eRk_add_eRk_of_closed`: a set of elements closed under the
  exchange arcs that contains `X₁(I)` and avoids `X₂(I)` certifies optimality of `I`.
* `Cslib.Algorithms.Lean.Matroid.exists_isShortestExchAugWalk`,
  `Cslib.Algorithms.Lean.Matroid.IsShortestExchAugWalk.nodup`: existence and simplicity of
  shortest augmenting walks.
* `Cslib.Algorithms.Lean.Matroid.IsShortestExchAugWalk.augment`: augmenting along a shortest
  augmenting walk gives a common independent set of size `I.card + 1` ([Schrijver2017],
  Theorem 10.6).
* `Cslib.Algorithms.Lean.Matroid.exists_separator_of_not_exists_exchAugWalk`: without an augmenting
  walk, the unreachable set attains the bound ([Schrijver2017], Theorem 10.7).
* `Cslib.Algorithms.Lean.Matroid.exists_commonIndep_card_eq_eRk_add_eRk`,
  `Cslib.Algorithms.Lean.Matroid.exists_commonIndep_card_eq_rk_add_rk`,
  `Cslib.Algorithms.Lean.Matroid.iSup_card_eq_iInf_eRk_add_eRk`,
  `Cslib.Algorithms.Lean.Matroid.iSup_encard_eq_iInf_eRk_add_eRk`: **Edmonds' matroid intersection
  theorem** ([Edmonds1970]; [Schrijver2017], Theorem 10.9).

## References

* [J. Edmonds, *Submodular Functions, Matroids, and Certain Polyhedra*][Edmonds1970]
* [E. L. Lawler, *Matroid Intersection Algorithms*][Lawler1975]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003],
  Chapter 41
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Sections 10.4–10.5
-/

public section

namespace Cslib.Algorithms.Lean.Matroid

open scoped symmDiff

/-! ### Common independent sets and weak duality -/

section WeakDuality

variable {α : Type*}

/-- `I : Finset α` is a common independent set of `M₁` and `M₂`. -/
@[expose] def IsCommonIndep (M₁ M₂ : Matroid α) (I : Finset α) : Prop :=
  M₁.Indep (I : Set α) ∧ M₂.Indep (I : Set α)

theorem IsCommonIndep.indep_left {M₁ M₂ : Matroid α} {I : Finset α}
    (h : IsCommonIndep M₁ M₂ I) : M₁.Indep (I : Set α) := h.1

theorem IsCommonIndep.indep_right {M₁ M₂ : Matroid α} {I : Finset α}
    (h : IsCommonIndep M₁ M₂ I) : M₂.Indep (I : Set α) := h.2

/-- The empty set is a common independent set of any two matroids. -/
@[simp] theorem isCommonIndep_empty (M₁ M₂ : Matroid α) : IsCommonIndep M₁ M₂ ∅ := by
  simp [IsCommonIndep]

/-- `I` is a maximum-cardinality common independent subset of `E : Finset α`. -/
@[expose] def IsMaxCommonIndep (M₁ M₂ : Matroid α) (E I : Finset α) : Prop :=
  I ⊆ E ∧ IsCommonIndep M₁ M₂ I ∧
    ∀ J : Finset α, J ⊆ E → IsCommonIndep M₁ M₂ J → J.card ≤ I.card

/-- **Weak duality for matroid intersection** (`Set` form): a set `I ⊆ X` independent in both `M₁`
and `M₂` has `I.encard ≤ M₁.eRk U + M₂.eRk (X \ U)` for every `U`. No finiteness is needed. -/
theorem encard_le_eRk_add_eRk {M₁ M₂ : Matroid α} {X I : Set α} (hIX : I ⊆ X)
    (h₁ : M₁.Indep I) (h₂ : M₂.Indep I) (U : Set α) :
    I.encard ≤ M₁.eRk U + M₂.eRk (X \ U) := by
  rw [← Set.encard_sdiff_add_encard_inter I U, add_comm]
  refine add_le_add ?_ ?_
  · rw [← (h₁.subset Set.inter_subset_left).eRk_eq_encard]
    exact M₁.eRk_mono Set.inter_subset_right
  · rw [← (h₂.subset Set.sdiff_subset).eRk_eq_encard]
    exact M₂.eRk_mono (Set.sdiff_subset_sdiff_left hIX)

/-- **Weak duality for matroid intersection** (`ℕ∞` rank): for any common independent subset `I ⊆ E`
and any `U : Finset α`, `(I.card : ℕ∞) ≤ M₁.eRk ↑U + M₂.eRk ↑(E \ U)`. -/
theorem IsCommonIndep.card_le_eRk_add_eRk [DecidableEq α] {M₁ M₂ : Matroid α} {E I : Finset α}
    (hI : IsCommonIndep M₁ M₂ I) (hIE : I ⊆ E) (U : Finset α) :
    (I.card : ℕ∞) ≤ M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  rw [← Set.encard_coe_eq_coe_finsetCard, Finset.coe_sdiff]
  exact encard_le_eRk_add_eRk (Finset.coe_subset.mpr hIE) hI.indep_left hI.indep_right _

/-- **Weak duality for matroid intersection** (`ℕ` rank): for any common independent subset `I ⊆ E`
and any `U : Finset α`, `I.card ≤ (M₁.eRk ↑U).toNat + (M₂.eRk ↑(E \ U)).toNat`. -/
theorem IsCommonIndep.card_le_rk_add_rk [DecidableEq α] {M₁ M₂ : Matroid α} {E I : Finset α}
    (hI : IsCommonIndep M₁ M₂ I) (hIE : I ⊆ E) (U : Finset α) :
    I.card ≤ (M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat := by
  have he := hI.card_le_eRk_add_eRk hIE U
  have h1_ne : M₁.eRk (U : Set α) ≠ ⊤ :=
    (M₁.isRkFinite_of_finite U.finite_toSet).eRk_lt_top.ne
  have h2_ne : M₂.eRk ((E \ U : Finset α) : Set α) ≠ ⊤ :=
    (M₂.isRkFinite_of_finite (E \ U).finite_toSet).eRk_lt_top.ne
  have hcast : (I.card : ℕ∞) ≤
      (((M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat : ℕ) : ℕ∞) := by
    rwa [Nat.cast_add, ENat.natCast_toNat h1_ne, ENat.natCast_toNat h2_ne]
  exact Nat.cast_le.mp hcast

/-- A common independent subset `I ⊆ E` attaining `M₁.eRk ↑U + M₂.eRk ↑(E \ U)` for some `U` is
maximum among all common independent subsets of `E`. -/
theorem isMaxCommonIndep_of_card_eq_eRk_add_eRk [DecidableEq α] {M₁ M₂ : Matroid α}
    {E I U : Finset α} (hIE : I ⊆ E) (hI : IsCommonIndep M₁ M₂ I)
    (heq : (I.card : ℕ∞) = M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α)) :
    IsMaxCommonIndep M₁ M₂ E I := by
  refine ⟨hIE, hI, fun J hJE hJ => ?_⟩
  have hle := hJ.card_le_eRk_add_eRk hJE U
  rw [← heq] at hle
  exact Nat.cast_le.mp hle

end WeakDuality

/-! ### Chordless exchange sequences and the unreachable-set certificate -/

section ExchangeTheory

variable {α : Type*} [DecidableEq α]

private theorem coe_insert_sdiff_singleton_eq {I : Finset α} {y x : α}
    (hyI : y ∉ (I : Set α)) (hxI : x ∈ I) :
    (insert y (I : Set α)) \ {x} = ((insert y (I.erase x) : Finset α) : Set α) := by
  ext z
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Finset.mem_coe, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨rfl | hzI, hne⟩
    · exact .inl rfl
    · exact .inr ⟨hne, hzI⟩
  · rintro (rfl | ⟨hne, hzI⟩)
    · exact ⟨.inl rfl, fun h => hyI (h ▸ hxI)⟩
    · exact ⟨.inr hzI, hne⟩

/-- Exchanging `k` distinct elements `x i ∈ I` of `insert y₀ I` for `k` distinct elements
`y i ∉ insert y₀ I` preserves its cardinality. -/
private theorem card_exchange {I : Finset α} {y₀ : α} {k : ℕ} {x y : Fin k → α}
    (hx_mem : ∀ i, x i ∈ I) (hx_inj : Function.Injective x)
    (hy_not : ∀ i, y i ∉ insert y₀ I) (hy_inj : Function.Injective y) :
    ((insert y₀ I \ Finset.univ.image x) ∪ Finset.univ.image y).card = (insert y₀ I).card := by
  have hX_sub : Finset.univ.image x ⊆ insert y₀ I := by
    simp only [Finset.image_subset_iff, Finset.mem_univ, forall_const]
    exact fun i => Finset.mem_insert_of_mem (hx_mem i)
  have hdisj : Disjoint (insert y₀ I \ Finset.univ.image x) (Finset.univ.image y) := by
    simp only [Finset.disjoint_right, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ hmem
    exact hy_not i (Finset.mem_sdiff.mp hmem).1
  have hX_card : (Finset.univ.image x).card = k := by
    rw [Finset.card_image_of_injective _ hx_inj, Finset.card_fin]
  have hY_card : (Finset.univ.image y).card = k := by
    rw [Finset.card_image_of_injective _ hy_inj, Finset.card_fin]
  have hk_le := hX_card ▸ Finset.card_le_card hX_sub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hX_sub, hX_card, hY_card]
  omega

/-- **Chordless exchange sequences preserve independence.** Let `insert y₀ I` be independent in `M`,
and let `x, y : Fin k → α` be injective families with `x i ∈ I` and `y i ∉ insert y₀ I` such that
* `¬ M.Indep ↑(insert (y i) I)`: each `y i` spans a fundamental circuit of `I`;
* `M.Indep ↑(insert (y i) (I.erase (x i)))`: `y i` can replace `x i`; and
* for all `i < j`, `¬ M.Indep ↑(insert (y j) (I.erase (x i)))`: there are no forward chords.

Then `(insert y₀ I \ {x i}) ∪ {y i}` is independent in `M`.

This is the matroid step of [Schrijver2017], Theorem 10.6. In the source, it is Lemma 10.2 applied
to the unique perfect matching `{x i, y i}` in the exchange graph `H(M, I)` (the triangular
no-chord condition gives uniqueness), followed by a rank argument that adds `y₀`. Here the
statement is proved directly, by downward induction on `i`, showing that every `x i` lies in the
closure of the new set. -/
theorem indep_exchange_chain {M : Matroid α} {I : Finset α} {y₀ : α} {k : ℕ}
    (hB_indep : M.Indep ((insert y₀ I : Finset α) : Set α))
    {x y : Fin k → α}
    (hx_mem : ∀ i, x i ∈ I)
    (hx_inj : Function.Injective x)
    (hy_not : ∀ i, y i ∉ insert y₀ I)
    (hy_inj : Function.Injective y)
    (hy_dep : ∀ i, ¬ M.Indep ((insert (y i) I : Finset α) : Set α))
    (hdiag : ∀ i, M.Indep ((insert (y i) (I.erase (x i)) : Finset α) : Set α))
    (hno_chord : ∀ i j : Fin k, i < j →
      ¬ M.Indep ((insert (y j) (I.erase (x i)) : Finset α) : Set α)) :
    M.Indep
      ((((insert y₀ I \ Finset.univ.image x) ∪ Finset.univ.image y : Finset α)) : Set α) := by
  let B : Finset α := insert y₀ I
  let Xset : Finset α := Finset.univ.image x
  let I' : Finset α := (B \ Xset) ∪ Finset.univ.image y
  have hI_indep : M.Indep (I : Set α) :=
    hB_indep.subset (Finset.coe_subset.mpr (Finset.subset_insert y₀ I))
  have hy_ground : ∀ i, y i ∈ M.E := fun i =>
    (hdiag i).subset_ground (by simp)
  have hI'_ground : (I' : Set α) ⊆ M.E := by
    intro a ha
    simp only [I', Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_sdiff,
      Finset.mem_coe] at ha
    rcases ha with ⟨haB, _⟩ | haY
    · exact hB_indep.subset_ground haB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haY
      exact hy_ground i
  have hmem_cl_I' : ∀ a ∈ I', a ∈ M.closure (I' : Set α) := fun a ha =>
    M.subset_closure_of_subset' Set.Subset.rfl hI'_ground ha
  -- Downward induction on `i` shows every `x i` lies in `M.closure ↑I'`: the fundamental circuit
  -- of `y i` in `I` contains `x i`, and its other elements are `y i`, elements of `B \ Xset`, or
  -- `x r` with `i < r` (an `x r` with `r < i` would be a forward chord).
  have hx_closure : ∀ i : Fin k, x i ∈ M.closure (I' : Set α) := by
    intro i
    induction i using WellFoundedGT.induction with
    | ind i ih =>
      have hyi_not_I : y i ∉ (I : Set α) := fun h => hy_not i (Finset.mem_insert_of_mem h)
      have hyi_cl : y i ∈ M.closure (I : Set α) := by
        rw [hI_indep.mem_closure_iff']
        refine ⟨hy_ground i, fun hind => absurd ?_ (hy_dep i)⟩
        rwa [Finset.coe_insert]
      have hmem_C : ∀ r, x r ∈ M.fundCircuit (y i) (I : Set α) ↔
          M.Indep ((insert (y i) (I.erase (x r)) : Finset α) : Set α) := fun r => by
        rw [hI_indep.mem_fundCircuit_iff hyi_cl hyi_not_I,
          coe_insert_sdiff_singleton_eq hyi_not_I (hx_mem r)]
      have hxi_C : x i ∈ M.fundCircuit (y i) (I : Set α) := (hmem_C i).mpr (hdiag i)
      have hsub_cl : M.fundCircuit (y i) (I : Set α) \ {x i} ⊆ M.closure (I' : Set α) := by
        intro z ⟨hzC, hzne⟩
        rcases Set.mem_insert_iff.mp (M.fundCircuit_subset_insert (y i) (I : Set α) hzC)
          with rfl | hzI
        · exact hmem_cl_I' (y i)
            (Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))
        · by_cases hzX : z ∈ Xset
          · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hzX
            have hri : r ≠ i := fun h => hzne (congrArg x h)
            have hnot_lt : ¬ r < i := fun hlt => hno_chord r i hlt ((hmem_C r).mp hzC)
            exact ih r (lt_of_le_of_ne (not_lt.mp hnot_lt) hri.symm)
          · exact hmem_cl_I' z (Finset.mem_union_left _
              (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hzI, hzX⟩))
      have hxi_in_cl_C : x i ∈ M.closure (M.fundCircuit (y i) (I : Set α) \ {x i}) :=
        ((hI_indep.fundCircuit_isCircuit hyi_cl hyi_not_I).sdiff_singleton_isBasis
          hxi_C).subset_closure hxi_C
      exact M.closure_subset_closure_of_subset_closure hsub_cl hxi_in_cl_C
  have hB_sub_cl : (B : Set α) ⊆ M.closure (I' : Set α) := by
    intro a ha
    by_cases haX : a ∈ Xset
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haX
      exact hx_closure i
    · exact hmem_cl_I' a (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, haX⟩))
  -- `I'` has as many elements as the independent set `B` it spans, so it is independent.
  have hcard_le_eRk : (I' : Set α).encard ≤ M.eRk (I' : Set α) := by
    rw [Set.encard_coe_eq_coe_finsetCard, card_exchange hx_mem hx_inj hy_not hy_inj,
      ← Set.encard_coe_eq_coe_finsetCard, ← hB_indep.eRk_eq_encard,
      ← M.eRk_closure_eq (I' : Set α)]
    exact M.eRk_mono hB_sub_cl
  exact (M.isRkFinite_of_finite I'.finite_toSet).indep_of_encard_le_eRk hcard_le_eRk

/-- Helper for unreachability duality: if `I : Finset α` is `M`-independent, `y ∉ I`, and
`M.Indep ↑(insert y S)`, then either `M.Indep ↑(insert y I)` or there exists `x ∈ I \ S` such that
`M.Indep ↑(insert y (I.erase x))`. -/
private theorem indep_insert_or_exists_erase {M : Matroid α} {I S : Finset α} {y : α}
    (hI : M.Indep (I : Set α)) (hyI : y ∉ I)
    (hyS : M.Indep ((insert y S : Finset α) : Set α)) :
    M.Indep ((insert y I : Finset α) : Set α) ∨
      ∃ x ∈ I \ S, M.Indep ((insert y (I.erase x) : Finset α) : Set α) := by
  by_cases hfull : M.Indep ((insert y I : Finset α) : Set α)
  · exact .inl hfull
  right
  -- Otherwise `y` closes a fundamental circuit `C ⊆ insert y I` of `I`. It is not contained in
  -- the independent set `insert y S`, so it has an element `x ∈ I \ S`, which `y` can replace.
  have hyI' : y ∉ (I : Set α) := hyI
  have hy_cl : y ∈ M.closure (I : Set α) := by
    rw [hI.mem_closure_iff']
    refine ⟨hyS.subset_ground (by simp), fun hind => absurd ?_ hfull⟩
    rwa [Finset.coe_insert]
  have hC := hI.fundCircuit_isCircuit hy_cl hyI'
  obtain ⟨x, hxC, hx_not⟩ :
      ∃ x ∈ M.fundCircuit y (I : Set α), x ∉ ((insert y S : Finset α) : Set α) :=
    Set.not_subset.mp fun hsub => hC.not_indep (hyS.subset hsub)
  have hxI : x ∈ I := by
    rcases Set.mem_insert_iff.mp (M.fundCircuit_subset_insert y (I : Set α) hxC) with rfl | hxI
    · exact absurd (by simp) hx_not
    · exact hxI
  have hxS : x ∉ S := fun hxS => hx_not (by simp [hxS])
  refine ⟨x, Finset.mem_sdiff.mpr ⟨hxI, hxS⟩, ?_⟩
  rw [← coe_insert_sdiff_singleton_eq hyI' hxI, ← hI.mem_fundCircuit_iff hy_cl hyI']
  exact hxC

/-- Helper for the unreachable-set certificate: let `I` be `M`-independent and `T` a finite set.
If no `y ∈ T \ I` extends `I` and no `y ∈ T \ I` replaces any `x ∈ I \ T`, then `I ∩ T` spans `T`:
`M.eRk ↑T = (I ∩ T).card`. Otherwise a `y ∈ T` raising the rank of `I ∩ T` gives one of these
exchanges by `indep_insert_or_exists_erase`. -/
private theorem eRk_eq_card_inter_of_forall_not_indep {M : Matroid α} {I T : Finset α}
    (hI : M.Indep (I : Set α))
    (hins : ∀ y ∈ T \ I, ¬ M.Indep ((insert y I : Finset α) : Set α))
    (hexch : ∀ y ∈ T \ I, ∀ x ∈ I \ T, ¬ M.Indep ((insert y (I.erase x) : Finset α) : Set α)) :
    M.eRk (T : Set α) = ((I ∩ T).card : ℕ∞) := by
  have hind : M.Indep ((I ∩ T : Finset α) : Set α) :=
    hI.subset (Finset.coe_subset.mpr Finset.inter_subset_left)
  refine le_antisymm ?_ ?_
  · by_contra hnot
    have hlt : M.eRk ((I ∩ T : Finset α) : Set α) < M.eRk (T : Set α) := by
      rw [hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard]
      exact lt_of_not_ge hnot
    obtain ⟨y, ⟨hyT, hy_not_IT⟩, hy_rk⟩ := M.exists_eRk_insert_eq_add_one_of_lt hlt
    have hyT : y ∈ T := Finset.mem_coe.mp hyT
    have hy_not_IT : y ∉ I ∩ T := fun h => hy_not_IT (Finset.mem_coe.mpr h)
    have hy_not_I : y ∉ I := fun hyI => hy_not_IT (Finset.mem_inter.mpr ⟨hyI, hyT⟩)
    have hy_indep : M.Indep ((insert y (I ∩ T) : Finset α) : Set α) := by
      refine (M.isRkFinite_of_finite (insert y (I ∩ T)).finite_toSet).indep_of_encard_le_eRk ?_
      rw [Finset.coe_insert, hy_rk, hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard,
        ← Finset.coe_insert, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_insert_of_notMem hy_not_IT, Nat.cast_add, Nat.cast_one]
    have hyTI : y ∈ T \ I := Finset.mem_sdiff.mpr ⟨hyT, hy_not_I⟩
    rcases indep_insert_or_exists_erase hI hy_not_I hy_indep
      with hfull | ⟨x, hx, hxch⟩
    · exact hins y hyTI hfull
    · obtain ⟨hxI, hx_not_IT⟩ := Finset.mem_sdiff.mp hx
      have hx_not_T : x ∉ T := fun hxT => hx_not_IT (Finset.mem_inter.mpr ⟨hxI, hxT⟩)
      exact hexch y hyTI x (Finset.mem_sdiff.mpr ⟨hxI, hx_not_T⟩) hxch
  · rw [← Set.encard_coe_eq_coe_finsetCard, ← hind.eRk_eq_encard]
    exact M.eRk_mono (Finset.coe_subset.mpr Finset.inter_subset_right)
/-- **The unreachable-set certificate** ([Schrijver2017], proof of Theorem 10.7): let `I ⊆ E` be a
common independent set of `M₁` and `M₂`. Let `R` contain the source set `X₁(I)`, avoid the sink set
`X₂(I)`, and be closed under the exchange arcs: `M₁`-arcs from `x ∈ R ∩ I` to `y ∈ E \ I`, and
`M₂`-arcs from `y ∈ R \ I` to `x ∈ I`. Then `I.card = M₁.eRk ↑(E \ R) + M₂.eRk ↑R`, so `I` and
the separator `U := E \ R` attain equality in weak duality. In the source, `U` is the set of
vertices not reachable from `X₁(I)`, and the two summands are (27) `r₁(U) = |I ∩ U|` and its `M₂`
counterpart `r₂(E \ U) = |I \ U|`. -/
theorem card_eq_eRk_add_eRk_of_closed {M₁ M₂ : Matroid α} {E I R : Finset α}
    (hIE : I ⊆ E) (hI : IsCommonIndep M₁ M₂ I)
    (hX1 : ∀ y ∈ E \ I, M₁.Indep ((insert y I : Finset α) : Set α) → y ∈ R)
    (hX2 : ∀ y ∈ R \ I, ¬ M₂.Indep ((insert y I : Finset α) : Set α))
    (hcl1 : ∀ x ∈ R ∩ I, ∀ y ∈ E \ I,
      M₁.Indep ((insert y (I.erase x) : Finset α) : Set α) → y ∈ R)
    (hcl2 : ∀ y ∈ R \ I, ∀ x ∈ I,
      M₂.Indep ((insert y (I.erase x) : Finset α) : Set α) → x ∈ R) :
    (I.card : ℕ∞) = M₁.eRk ((E \ R : Finset α) : Set α) + M₂.eRk (R : Set α) := by
  -- `I \ R` spans `E \ R` in `M₁`: an element of `E \ R` extending `I \ R` would be a source, or
  -- the head of an `M₁`-arc out of `R ∩ I`.
  have hrk1 : M₁.eRk ((E \ R : Finset α) : Set α) = ((I ∩ (E \ R)).card : ℕ∞) := by
    refine eRk_eq_card_inter_of_forall_not_indep hI.indep_left (fun y hy hind => ?_)
      (fun y hy x hx hind => ?_)
    · obtain ⟨hyER, hy_not_I⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨hyE, hy_not_R⟩ := Finset.mem_sdiff.mp hyER
      exact hy_not_R (hX1 y (Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩) hind)
    · obtain ⟨hyER, hy_not_I⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨hyE, hy_not_R⟩ := Finset.mem_sdiff.mp hyER
      obtain ⟨hxI, hx_not_ER⟩ := Finset.mem_sdiff.mp hx
      have hxR : x ∈ R := by
        by_contra hxR
        exact hx_not_ER (Finset.mem_sdiff.mpr ⟨hIE hxI, hxR⟩)
      exact hy_not_R (hcl1 x (Finset.mem_inter.mpr ⟨hxR, hxI⟩) y
        (Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩) hind)
  -- `I ∩ R` spans `R` in `M₂`: an element of `R` extending `I ∩ R` would be a sink, or the tail of
  -- an `M₂`-arc into `I \ R`.
  have hrk2 : M₂.eRk (R : Set α) = ((I ∩ R).card : ℕ∞) := by
    refine eRk_eq_card_inter_of_forall_not_indep hI.indep_right hX2 (fun y hy x hx hind => ?_)
    obtain ⟨hxI, hx_not_R⟩ := Finset.mem_sdiff.mp hx
    exact hx_not_R (hcl2 y hy x hxI hind)
  have hcard : (I ∩ (E \ R)).card + (I ∩ R).card = I.card := by
    rw [← Finset.inter_sdiff_assoc, Finset.inter_eq_left.mpr hIE, add_comm,
      Finset.card_inter_add_card_sdiff]
  rw [hrk1, hrk2, ← Nat.cast_add, hcard]

end ExchangeTheory

/-! ### The exchange digraph, shortest augmenting walks, and Edmonds' theorem -/

section ExchangeWalkAugmentation

variable {α : Type*} [DecidableEq α]

/-- `y` lies in the source set `X₁(I)` of the exchange digraph ([Schrijver2017], (24)):
`y ∈ E \ I` and `insert y I` is independent in `M₁`. -/
@[expose] def IsExchSource (M₁ : Matroid α) (E I : Finset α) (y : α) : Prop :=
  y ∈ E \ I ∧ M₁.Indep ((insert y I : Finset α) : Set α)

/-- `y` lies in the sink set `X₂(I)` of the exchange digraph ([Schrijver2017], (24)):
`y ∈ E \ I` and `insert y I` is independent in `M₂`. -/
@[expose] def IsExchSink (M₂ : Matroid α) (E I : Finset α) (y : α) : Prop :=
  y ∈ E \ I ∧ M₂.Indep ((insert y I : Finset α) : Set α)

/-- `u → v` is an arc of the exchange digraph `H(M₁, M₂, I)` on `E` ([Schrijver2017], (23)):
* from `u ∈ I` to `v ∈ E \ I` when `insert v (I.erase u)` is independent in `M₁`;
* from `u ∈ E \ I` to `v ∈ I` when `insert u (I.erase v)` is independent in `M₂`. -/
@[expose] def IsExchArc (M₁ M₂ : Matroid α) (E I : Finset α) (u v : α) : Prop :=
  (u ∈ I ∧ v ∈ E \ I ∧ M₁.Indep ((insert v (I.erase u) : Finset α) : Set α)) ∨
    (u ∈ E \ I ∧ v ∈ I ∧ M₂.Indep ((insert u (I.erase v) : Finset α) : Set α))

/-- `p` is a directed walk in the exchange digraph `H(M₁, M₂, I)` on `E`. -/
@[expose] def IsExchWalk (M₁ M₂ : Matroid α) (E I : Finset α) (p : List α) : Prop :=
  (∀ z ∈ p, z ∈ E) ∧ List.IsChain (IsExchArc M₁ M₂ E I) p

/-- `p` is a nonempty walk in `H(M₁, M₂, I)` from the source set `X₁(I)` to the sink set `X₂(I)`.
A single vertex of `X₁(I) ∩ X₂(I)` is such a walk (of length `0` in the source's arc count). -/
@[expose] def IsExchAugWalk (M₁ M₂ : Matroid α) (E I : Finset α) (p : List α) : Prop :=
  ∃ hne : p ≠ [], IsExchSource M₁ E I (p.head hne) ∧ IsExchSink M₂ E I (p.getLast hne) ∧
    IsExchWalk M₁ M₂ E I p

/-- `p` is an `X₁(I)`-to-`X₂(I)` walk in `H(M₁, M₂, I)` with the minimum number of vertices. -/
@[expose] def IsShortestExchAugWalk (M₁ M₂ : Matroid α) (E I : Finset α) (p : List α) : Prop :=
  IsExchAugWalk M₁ M₂ E I p ∧ ∀ q : List α, IsExchAugWalk M₁ M₂ E I q → p.length ≤ q.length

/-- If some `X₁(I)`-to-`X₂(I)` walk exists, then a shortest one exists. -/
theorem exists_isShortestExchAugWalk {M₁ M₂ : Matroid α} {E I : Finset α}
    (hex : ∃ p : List α, IsExchAugWalk M₁ M₂ E I p) :
    ∃ p : List α, IsShortestExchAugWalk M₁ M₂ E I p := by
  classical
  have hex_len : ∃ len : ℕ, ∃ p : List α, p.length = len ∧ IsExchAugWalk M₁ M₂ E I p := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p.length, p, rfl, hp⟩
  obtain ⟨p, hp_len, hp_aug⟩ := Nat.find_spec hex_len
  refine ⟨p, hp_aug, fun q hq => ?_⟩
  rw [hp_len]
  exact Nat.find_min' hex_len ⟨q, rfl, hq⟩

private theorem mem_symmDiff_toFinset {I : Finset α} {p : List α} (a : α) :
    a ∈ I ∆ p.toFinset ↔ (a ∈ I ↔ a ∉ p) := by
  rw [Finset.mem_symmDiff, List.mem_toFinset]
  by_cases haI : a ∈ I <;> by_cases hap : a ∈ p <;> simp [haI, hap]

private theorem isExchArc_iff_mem_flip {M₁ M₂ : Matroid α} {E I : Finset α} {u v : α}
    (harc : IsExchArc M₁ M₂ E I u v) : (u ∈ I ↔ v ∉ I) := by
  rcases harc with ⟨huI, hvE, _⟩ | ⟨huE, hvI, _⟩
  · exact ⟨fun _ => (Finset.mem_sdiff.mp hvE).2, fun _ => huI⟩
  · exact ⟨fun huI => absurd huI (Finset.mem_sdiff.mp huE).2, fun hv_not => absurd hvI hv_not⟩

private theorem isExchWalk_parity {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hchain : List.IsChain (IsExchArc M₁ M₂ E I) p)
    (hne : p ≠ []) (h0 : p.head hne ∉ I) :
    ∀ t (ht : t < p.length), (p[t]'ht ∈ I ↔ t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    intro ht
    have hhead : p[0]'ht = p.head hne := (List.head_eq_getElem hne).symm
    rw [hhead]
    simp [h0]
  | succ t ih =>
    intro ht
    have ht_lt : t < p.length := Nat.lt_of_succ_lt ht
    have harc : IsExchArc M₁ M₂ E I (p[t]'ht_lt) (p[t + 1]'ht) :=
      List.IsChain.getElem hchain t (by omega)
    have hflip := isExchArc_iff_mem_flip harc
    have iht := ih ht_lt
    by_cases hm : p[t]'ht_lt ∈ I
    · have ht_odd : t % 2 = 1 := iht.mp hm
      have hv_not : p[t + 1]'ht ∉ I := hflip.mp hm
      exact ⟨fun h => absurd h hv_not, fun h => by omega⟩
    · have ht_even : t % 2 ≠ 1 := fun h => hm (iht.mpr h)
      have hv_in : p[t + 1]'ht ∈ I := by
        by_contra hv_not
        exact hm (hflip.mpr hv_not)
      exact ⟨fun _ => by omega, fun _ => hv_in⟩

omit [DecidableEq α] in
private theorem isChain_take_append_drop {R : α → α → Prop} {p : List α}
    (hp : List.IsChain R p) {i j : ℕ} (hi : i < p.length) (hj : j < p.length)
    (harc : R (p[i]'hi) (p[j]'hj)) :
    List.IsChain R (p.take (i + 1) ++ p.drop j) := by
  refine List.IsChain.append (hp.take (i + 1)) (hp.drop j) ?_
  intro x hx y hy
  have htake_ne : p.take (i + 1) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [Nat.min_eq_left (Nat.succ_le_of_lt hi)] at hlen
  have hdrop_ne : p.drop j ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.mp h
    omega
  rw [Option.mem_def, List.getLast?_eq_some_getLast htake_ne, Option.some.injEq] at hx
  rw [Option.mem_def, List.head?_eq_some_head hdrop_ne, Option.some.injEq] at hy
  subst hx hy
  have hlast : (p.take (i + 1)).getLast htake_ne = p[i]'hi := by
    rw [List.getLast_eq_getElem]
    simp [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  have hhead : (p.drop j).head hdrop_ne = p[j]'hj := by
    rw [List.head_drop]
  simpa [hlast, hhead] using harc

private theorem isExchAugWalk_take_append_drop {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hp : IsExchAugWalk M₁ M₂ E I p) {i j : ℕ} (hi : i < p.length) (hj : j < p.length)
    (harc : IsExchArc M₁ M₂ E I (p[i]'hi) (p[j]'hj)) :
    IsExchAugWalk M₁ M₂ E I (p.take (i + 1) ++ p.drop j) := by
  obtain ⟨hne, hX1, hX2, hmemE, hchain⟩ := hp
  have htake_ne : p.take (i + 1) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [Nat.min_eq_left (Nat.succ_le_of_lt hi)] at hlen
  have hdrop_ne : p.drop j ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.mp h
    omega
  have hq_ne : p.take (i + 1) ++ p.drop j ≠ [] := List.append_ne_nil_of_left_ne_nil htake_ne _
  refine ⟨hq_ne, ?_, ?_, ?_, isChain_take_append_drop hchain hi hj harc⟩
  · have hhead : (p.take (i + 1) ++ p.drop j).head hq_ne = p.head hne := by
      rw [List.head_append_of_ne_nil htake_ne, List.head_take]
    rwa [hhead]
  · have hlast : (p.take (i + 1) ++ p.drop j).getLast hq_ne = p.getLast hne := by
      rw [List.getLast_append_of_ne_nil _ hdrop_ne, List.getLast_drop]
    rwa [hlast]
  · intro z hz
    rcases List.mem_append.mp hz with hzt | hzd
    · exact hmemE z (List.mem_of_mem_take hzt)
    · exact hmemE z (List.mem_of_mem_drop hzd)

/-- Reversing every arc of `H(M₁, M₂, I)` gives `H(M₂, M₁, I)`. -/
private theorem isExchArc_swap {M₁ M₂ : Matroid α} {E I : Finset α} {u v : α} :
    IsExchArc M₂ M₁ E I v u ↔ IsExchArc M₁ M₂ E I u v := by
  unfold IsExchArc
  constructor <;> rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩)
  exacts [.inr ⟨h₂, h₁, h₃⟩, .inl ⟨h₂, h₁, h₃⟩, .inr ⟨h₂, h₁, h₃⟩, .inl ⟨h₂, h₁, h₃⟩]

/-- Reading an `X₁(I)`-to-`X₂(I)` walk of `H(M₁, M₂, I)` backwards gives an augmenting walk of
`H(M₂, M₁, I)`: its sources and sinks trade places. -/
private theorem IsExchAugWalk.reverse {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hp : IsExchAugWalk M₁ M₂ E I p) : IsExchAugWalk M₂ M₁ E I p.reverse := by
  obtain ⟨hne, hX1, hX2, hmemE, hchain⟩ := hp
  have hne' : p.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hne
  refine ⟨hne', ?_, ?_, fun z hz => hmemE z (List.mem_reverse.mp hz), ?_⟩
  · rw [List.head_reverse]
    exact hX2
  · rw [List.getLast_reverse]
    exact hX1
  · exact List.isChain_reverse.mpr (hchain.imp fun _ _ h => isExchArc_swap.mpr h)

/-- The reverse of a shortest augmenting walk of `H(M₁, M₂, I)` is a shortest augmenting walk of
`H(M₂, M₁, I)`. -/
private theorem IsShortestExchAugWalk.reverse {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hshort : IsShortestExchAugWalk M₁ M₂ E I p) : IsShortestExchAugWalk M₂ M₁ E I p.reverse := by
  refine ⟨hshort.1.reverse, fun q hq => ?_⟩
  have hle := hshort.2 q.reverse hq.reverse
  rwa [List.length_reverse, ← List.length_reverse (as := q)]

/-- A shortest augmenting walk has no shortcuts: an arc from `p[i]` to `p[j]` forces
`j ≤ i + 1`, since otherwise `p[0..i] ++ p[j..]` would be a shorter augmenting walk. -/
private theorem IsShortestExchAugWalk.le_succ_of_isExchArc {M₁ M₂ : Matroid α} {E I : Finset α}
    {p : List α} (hshort : IsShortestExchAugWalk M₁ M₂ E I p) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) (harc : IsExchArc M₁ M₂ E I (p[i]'hi) (p[j]'hj)) : j ≤ i + 1 := by
  have hlen := hshort.2 _ (isExchAugWalk_take_append_drop hshort.1 hi hj harc)
  rw [List.length_append, List.length_take, Nat.min_eq_left (by omega), List.length_drop] at hlen
  omega

/-- Only the first vertex of a shortest augmenting walk is a source: if `p[j] ∈ X₁(I)`, then
`p[j..]` is an augmenting walk, so `j = 0`. -/
private theorem IsShortestExchAugWalk.eq_zero_of_isExchSource {M₁ M₂ : Matroid α}
    {E I : Finset α} {p : List α} (hshort : IsShortestExchAugWalk M₁ M₂ E I p) {j : ℕ}
    (hj : j < p.length) (hsrc : IsExchSource M₁ E I (p[j]'hj)) : j = 0 := by
  obtain ⟨⟨hne, -, hX2, hmemE, hchain⟩, hmin⟩ := hshort
  have hdrop_ne : p.drop j ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.mp h
    omega
  have haug : IsExchAugWalk M₁ M₂ E I (p.drop j) := by
    refine ⟨hdrop_ne, ?_, ?_, fun z hz => hmemE z (List.mem_of_mem_drop hz), hchain.drop j⟩
    · rwa [List.head_drop]
    · rwa [List.getLast_drop]
  have hlen := hmin _ haug
  rw [List.length_drop] at hlen
  omega

/-- A shortest augmenting walk visits no vertex twice: a repeated vertex would give a source after
the first position or a shortcut arc. -/
theorem IsShortestExchAugWalk.nodup {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hshort : IsShortestExchAugWalk M₁ M₂ E I p) : p.Nodup := by
  obtain ⟨hne, hX1, -, -, hchain⟩ := hshort.1
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  dsimp only at heq
  simp only [Fin.mk.injEq]
  by_contra hne_idx
  wlog hij : i < j generalizing i j
  · exact this j hj i hi heq.symm (Ne.symm hne_idx) (by omega)
  cases i with
  | zero =>
    -- `p[j] = p[0]` is a source, so `j = 0`.
    have hsrc : IsExchSource M₁ E I (p[j]'hj) := by
      rwa [← heq, ← List.head_eq_getElem hne]
    have := hshort.eq_zero_of_isExchSource hj hsrc
    omega
  | succ i =>
    -- The arc `p[i] → p[i + 1] = p[j]` is a shortcut.
    have harc : IsExchArc M₁ M₂ E I (p[i]'(by omega)) (p[j]'hj) := by
      rw [← heq]
      exact List.IsChain.getElem hchain i (by omega)
    have := hshort.le_succ_of_isExchArc (by omega) hj harc
    omega

/-- A shortest augmenting walk alternates between `E \ I` and `I`, starting and ending outside `I`,
so it has an odd number `2k + 1` of vertices. -/
private theorem IsShortestExchAugWalk.length_eq {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hshort : IsShortestExchAugWalk M₁ M₂ E I p) :
    ∃ k, p.length = 2 * k + 1 ∧ ∀ t (ht : t < p.length), (p[t]'ht ∈ I ↔ t % 2 = 1) := by
  obtain ⟨⟨hne, hX1, hX2, -, hchain⟩, -⟩ := hshort
  have hpar := isExchWalk_parity hchain hne (Finset.mem_sdiff.mp hX1.1).2
  have hlen_pos : 0 < p.length := List.length_pos_of_ne_nil hne
  have hlast : p[p.length - 1]'(by omega) ∉ I := by
    rw [← List.getLast_eq_getElem hne]
    exact (Finset.mem_sdiff.mp hX2.1).2
  have hodd : ¬ (p.length - 1) % 2 = 1 := fun h => hlast ((hpar _ _).mpr h)
  exact ⟨(p.length - 1) / 2, by omega, hpar⟩

/-- **The `M₁` half of the augmentation.** Read a shortest augmenting walk `p` of `H(M₁, M₂, I)` as
`y₀, x₀, y₁, x₁, …, y_k` (so `x i = p[2i+1] ∈ I` and `y i = p[2i+2] ∉ I`). Then `y₀ ∈ X₁(I)`, each
`x i → y i` is an `M₁`-arc, minimality rules out the chords `x i → y j` (`i < j`) and the sources
`y i ∈ X₁(I)`, so `indep_exchange_chain` makes `I ∆ p` independent in `M₁`; it has `I.card + 1`
elements. The `M₂` half is this lemma applied to the reversed walk. -/
private theorem IsShortestExchAugWalk.indep_left_symmDiff {M₁ M₂ : Matroid α} {E I : Finset α}
    {p : List α} (hshort : IsShortestExchAugWalk M₁ M₂ E I p) :
    M₁.Indep ((I ∆ p.toFinset : Finset α) : Set α) ∧ (I ∆ p.toFinset).card = I.card + 1 := by
  have hnodup : p.Nodup := hshort.nodup
  obtain ⟨k, hlen, hpar⟩ := hshort.length_eq
  obtain ⟨hne, hX1, -, hmemE, hchain⟩ := hshort.1
  let y₀ : α := p[0]'(by omega)
  let x : Fin k → α := fun i => p[2 * i.1 + 1]'(by omega)
  let y : Fin k → α := fun i => p[2 * i.1 + 2]'(by omega)
  have hy₀ : IsExchSource M₁ E I y₀ := by
    rw [show y₀ = p.head hne from (List.head_eq_getElem hne).symm]
    exact hX1
  have hx_mem : ∀ i, x i ∈ I := fun i => (hpar _ _).mpr (by omega)
  have hy_not_I : ∀ i, y i ∉ I := fun i h => by
    have := (hpar _ _).mp h
    omega
  have hx_inj : Function.Injective x := fun i j hij => by
    have := (hnodup.getElem_inj_iff).mp hij
    exact Fin.ext (by omega)
  have hy_inj : Function.Injective y := fun i j hij => by
    have := (hnodup.getElem_inj_iff).mp hij
    exact Fin.ext (by omega)
  have hy_not : ∀ i, y i ∉ insert y₀ I := by
    intro i hmem
    rcases Finset.mem_insert.mp hmem with heq | hyI
    · have := (hnodup.getElem_inj_iff).mp heq
      omega
    · exact hy_not_I i hyI
  have hy_E : ∀ i, y i ∈ E \ I := fun i =>
    Finset.mem_sdiff.mpr ⟨hmemE _ (List.getElem_mem _), hy_not_I i⟩
  -- Minimality: no later `y i` is a source, and there are no forward chords.
  have hy_dep : ∀ i, ¬ M₁.Indep ((insert (y i) I : Finset α) : Set α) := fun i hind => by
    have := hshort.eq_zero_of_isExchSource _ ⟨hy_E i, hind⟩
    omega
  have hdiag : ∀ i, M₁.Indep ((insert (y i) (I.erase (x i)) : Finset α) : Set α) := by
    intro i
    rcases (List.IsChain.getElem hchain (2 * i.1 + 1) (by omega) :
        IsExchArc M₁ M₂ E I (x i) (y i)) with ⟨_, _, hind⟩ | ⟨hx_not_I, _, _⟩
    · exact hind
    · exact absurd (hx_mem i) (Finset.mem_sdiff.mp hx_not_I).2
  have hno_chord : ∀ i j : Fin k, i < j →
      ¬ M₁.Indep ((insert (y j) (I.erase (x i)) : Finset α) : Set α) := by
    intro i j hij hind
    have := hshort.le_succ_of_isExchArc (i := 2 * i.1 + 1) (j := 2 * j.1 + 2) (by omega)
      (by omega) (.inl ⟨hx_mem i, hy_E j, hind⟩)
    have hij' : i.1 < j.1 := hij
    omega
  -- The vertices of `p` are `y₀`, the `x i` and the `y i`, so `I ∆ p` is
  -- `(insert y₀ I \ {x i}) ∪ {y i}`.
  have hmem_p : ∀ a, a ∈ p ↔ a = y₀ ∨ (∃ i, x i = a) ∨ ∃ i, y i = a := by
    intro a
    refine ⟨fun hap => ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hap
      rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
      · rcases s with _ | s
        · exact .inl rfl
        · exact .inr (.inr ⟨⟨s, by omega⟩, rfl⟩)
      · exact .inr (.inl ⟨⟨s, by omega⟩, rfl⟩)
    · rintro (rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩) <;> exact List.getElem_mem _
  have hy₀_not_I : y₀ ∉ I := (Finset.mem_sdiff.mp hy₀.1).2
  have hI' : I ∆ p.toFinset = (insert y₀ I \ Finset.univ.image x) ∪ Finset.univ.image y := by
    ext a
    rw [mem_symmDiff_toFinset, hmem_p]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and]
    by_cases haI : a ∈ I
    · have hne : a ≠ y₀ := fun h => hy₀_not_I (h ▸ haI)
      have hny : ¬∃ i, y i = a := fun ⟨i, hi⟩ => hy_not_I i (hi ▸ haI)
      simp [haI, hne, hny]
    · have hnx : ¬∃ i, x i = a := fun ⟨i, hi⟩ => haI (hi ▸ hx_mem i)
      simp [haI, hnx, or_iff_not_imp_left]
  rw [hI']
  refine ⟨indep_exchange_chain hy₀.2 hx_mem hx_inj hy_not hy_inj hy_dep hdiag hno_chord, ?_⟩
  rw [card_exchange hx_mem hx_inj hy_not hy_inj, Finset.card_insert_of_notMem hy₀_not_I]

/-- **Augmenting along a shortest walk** ([Schrijver2017], Theorem 10.6): if `I ⊆ E` and `p` is a
shortest `X₁(I)`-to-`X₂(I)` walk in the exchange digraph `H(M₁, M₂, I)`, then `I ∆ p` is a common
independent subset of `E` with one more element than `I`. The walk alternates between `E \ I` and
`I`, so `I ∆ p` is the source's `(I \ {z₁, …, zₘ}) ∪ {y₀, …, yₘ}`. Minimality makes the walk
chordless in both directions, and `indep_exchange_chain` applies once to `M₁` (reading the walk
forwards) and once to `M₂` (reading it backwards). The independence of `I` itself is not needed:
it follows from `y₀ ∈ X₁(I)` and `yₘ ∈ X₂(I)`. -/
theorem IsShortestExchAugWalk.augment {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hshort : IsShortestExchAugWalk M₁ M₂ E I p) (hIE : I ⊆ E) :
    I ∆ p.toFinset ⊆ E ∧
      IsCommonIndep M₁ M₂ (I ∆ p.toFinset) ∧
      (I ∆ p.toFinset).card = I.card + 1 := by
  obtain ⟨hind₁, hcard⟩ := hshort.indep_left_symmDiff
  -- The `M₂` half: read the walk backwards, as a shortest walk of `H(M₂, M₁, I)`.
  have hind₂ := hshort.reverse.indep_left_symmDiff.1
  rw [List.toFinset_reverse] at hind₂
  refine ⟨fun a ha => ?_, ⟨hind₁, hind₂⟩, hcard⟩
  obtain ⟨⟨-, -, -, hmemE, -⟩, -⟩ := hshort
  rw [mem_symmDiff_toFinset] at ha
  by_cases hap : a ∈ p
  · exact hmemE a hap
  · exact hIE (ha.mpr hap)

/-- **No augmenting walk certifies optimality** ([Schrijver2017], Theorem 10.7): if `I ⊆ E` is a
common independent set and the exchange digraph `H(M₁, M₂, I)` has no `X₁(I)`-to-`X₂(I)` walk,
then the set `U ⊆ E` of vertices not reachable from `X₁(I)` satisfies
`(I.card : ℕ∞) = M₁.eRk ↑U + M₂.eRk ↑(E \ U)`. -/
theorem exists_separator_of_not_exists_exchAugWalk {M₁ M₂ : Matroid α} {E I : Finset α}
    (hIE : I ⊆ E) (hI : IsCommonIndep M₁ M₂ I)
    (hno : ¬ ∃ p : List α, IsExchAugWalk M₁ M₂ E I p) :
    ∃ U : Finset α, U ⊆ E ∧
      (I.card : ℕ∞) = M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  classical
  let ReachPred (z : α) : Prop :=
    ∃ q : List α, ∃ hne : q ≠ [],
      IsExchSource M₁ E I (q.head hne) ∧ q.getLast hne = z ∧ IsExchWalk M₁ M₂ E I q
  let R : Finset α := E.filter ReachPred
  have hRE : R ⊆ E := Finset.filter_subset _ E
  have hmemR : ∀ z : α, z ∈ R ↔ z ∈ E ∧ ReachPred z := fun _ => Finset.mem_filter
  have hX1_in_R : ∀ y ∈ E \ I, M₁.Indep ((insert y I : Finset α) : Set α) → y ∈ R := by
    intro y hyE hind
    rw [hmemR]
    refine ⟨(Finset.mem_sdiff.mp hyE).1, [y], List.cons_ne_nil y [], ⟨hyE, hind⟩, rfl, ?_⟩
    refine ⟨fun z hz => ?_, List.isChain_singleton y⟩
    simp only [List.mem_singleton] at hz
    subst hz
    exact (Finset.mem_sdiff.mp hyE).1
  have hX2_disj : ∀ y ∈ R \ I, ¬ M₂.Indep ((insert y I : Finset α) : Set α) := by
    intro y hyRI hind₂
    obtain ⟨hyR, hy_not_I⟩ := Finset.mem_sdiff.mp hyRI
    obtain ⟨hyE, q, hne, hq1, hqlast, hqwalk⟩ := (hmemR y).mp hyR
    exact hno ⟨q, hne, hq1, hqlast.symm ▸ ⟨Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩, hind₂⟩, hqwalk⟩
  have extend_walk : ∀ u ∈ R, ∀ v ∈ E, IsExchArc M₁ M₂ E I u v → v ∈ R := by
    intro u huR v hvE harc
    obtain ⟨_, q, hne, hq1, hqlast, hqmem, hqchain⟩ := (hmemR u).mp huR
    rw [hmemR]
    have hq'_ne : q ++ [v] ≠ [] := List.append_ne_nil_of_right_ne_nil q (List.cons_ne_nil v [])
    refine ⟨hvE, q ++ [v], hq'_ne, ?_, ?_, ?_, ?_⟩
    · rwa [List.head_append_of_ne_nil hne]
    · simp
    · intro z hz
      rcases List.mem_append.mp hz with hzq | hzv
      · exact hqmem z hzq
      · simp only [List.mem_singleton] at hzv
        exact hzv ▸ hvE
    · refine List.IsChain.append hqchain (List.isChain_singleton v) ?_
      intro x hx y hy
      rw [Option.mem_def, List.getLast?_eq_some_getLast hne, Option.some.injEq] at hx
      simp only [Option.mem_def, List.head?_cons, Option.some.injEq] at hy
      subst hx hy
      rwa [hqlast]
  have hcl1 : ∀ x ∈ R ∩ I, ∀ y ∈ E \ I,
      M₁.Indep ((insert y (I.erase x) : Finset α) : Set α) → y ∈ R := by
    intro x hxRI y hyEI hind
    exact extend_walk x (Finset.mem_inter.mp hxRI).1 y (Finset.mem_sdiff.mp hyEI).1
      (.inl ⟨(Finset.mem_inter.mp hxRI).2, hyEI, hind⟩)
  have hcl2 : ∀ y ∈ R \ I, ∀ x ∈ I,
      M₂.Indep ((insert y (I.erase x) : Finset α) : Set α) → x ∈ R := by
    intro y hyRI x hxI hind
    have hyR : y ∈ R := (Finset.mem_sdiff.mp hyRI).1
    have hy_not_I : y ∉ I := (Finset.mem_sdiff.mp hyRI).2
    have hyE : y ∈ E := hRE hyR
    exact extend_walk y hyR x (hIE hxI)
      (.inr ⟨Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩, hxI, hind⟩)
  refine ⟨E \ R, Finset.sdiff_subset, ?_⟩
  rw [Finset.sdiff_sdiff_eq_self hRE]
  exact card_eq_eRk_add_eRk_of_closed hIE hI hX1_in_R hX2_disj hcl1 hcl2

private theorem exists_commonIndep_card_eq_aux (M₁ M₂ : Matroid α) (E : Finset α) :
    ∀ fuel : ℕ, ∀ I : Finset α, I ⊆ E → IsCommonIndep M₁ M₂ I → E.card - I.card ≤ fuel →
      ∃ J U : Finset α, J ⊆ E ∧ U ⊆ E ∧ IsMaxCommonIndep M₁ M₂ E J ∧
        (J.card : ℕ∞) = M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  intro fuel
  induction fuel with
  | zero =>
    intro I hIE hI hrem
    have hIE_eq : I = E :=
      Finset.eq_of_subset_of_card_le hIE (by have := Finset.card_le_card hIE; omega)
    have hno : ¬ ∃ p : List α, IsExchAugWalk M₁ M₂ E I p := by
      rintro ⟨p, hne, hX1, _, _⟩
      have hy := hX1.1
      rw [hIE_eq, sdiff_self] at hy
      exact Finset.notMem_empty _ hy
    obtain ⟨U, hUE, heq⟩ := exists_separator_of_not_exists_exchAugWalk hIE hI hno
    exact ⟨I, U, hIE, hUE, isMaxCommonIndep_of_card_eq_eRk_add_eRk hIE hI heq, heq⟩
  | succ fuel ih =>
    intro I hIE hI hrem
    by_cases hex : ∃ p : List α, IsExchAugWalk M₁ M₂ E I p
    · obtain ⟨p, hshort⟩ := exists_isShortestExchAugWalk hex
      obtain ⟨hI'E, hI', hI'card⟩ := hshort.augment hIE
      have hI'_le_E : (I ∆ p.toFinset).card ≤ E.card := Finset.card_le_card hI'E
      exact ih (I ∆ p.toFinset) hI'E hI' (by omega)
    · obtain ⟨U, hUE, heq⟩ := exists_separator_of_not_exists_exchAugWalk hIE hI hex
      exact ⟨I, U, hIE, hUE, isMaxCommonIndep_of_card_eq_eRk_add_eRk hIE hI heq, heq⟩

/-- **Edmonds' matroid intersection theorem** (`ℕ∞` rank form; [Edmonds1970]; [Schrijver2017],
Theorem 10.9; [Schrijver2003], Chapter 41): for matroids `M₁ M₂ : Matroid α` and a finite candidate
ground set `E : Finset α`, some maximum common independent subset `I ⊆ E` and some `U ⊆ E` satisfy
`(I.card : ℕ∞) = M₁.eRk ↑U + M₂.eRk ↑(E \ U)`. Together with weak duality
(`IsCommonIndep.card_le_eRk_add_eRk`), the maximum equals the minimum; see
`iSup_card_eq_iInf_eRk_add_eRk`. The proof is the augmenting-path algorithm: start from `∅`,
augment along shortest exchange walks (`IsShortestExchAugWalk.augment`) until none exists, then
read off `U` (`exists_separator_of_not_exists_exchAugWalk`). -/
theorem exists_commonIndep_card_eq_eRk_add_eRk (M₁ M₂ : Matroid α) (E : Finset α) :
    ∃ I U : Finset α, U ⊆ E ∧ IsMaxCommonIndep M₁ M₂ E I ∧
      (I.card : ℕ∞) = M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  obtain ⟨I, U, -, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_aux M₁ M₂ E E.card ∅
    (Finset.empty_subset E) (isCommonIndep_empty M₁ M₂) (by simp)
  exact ⟨I, U, hUE, hmax, heq⟩

/-- **Edmonds' matroid intersection theorem** (`ℕ` rank form): some maximum common independent
subset `I ⊆ E` and some `U ⊆ E` satisfy `I.card = (M₁.eRk ↑U).toNat + (M₂.eRk ↑(E \ U)).toNat`.
The ranks are finite because `E` is. -/
theorem exists_commonIndep_card_eq_rk_add_rk (M₁ M₂ : Matroid α) (E : Finset α) :
    ∃ I U : Finset α, U ⊆ E ∧ IsMaxCommonIndep M₁ M₂ E I ∧
      I.card = (M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat := by
  obtain ⟨I, U, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ E
  have h1_ne : M₁.eRk (U : Set α) ≠ ⊤ :=
    (M₁.isRkFinite_of_finite U.finite_toSet).eRk_lt_top.ne
  have h2_ne : M₂.eRk ((E \ U : Finset α) : Set α) ≠ ⊤ :=
    (M₂.isRkFinite_of_finite (E \ U).finite_toSet).eRk_lt_top.ne
  have hcast : (I.card : ℕ∞) =
      (((M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat : ℕ) : ℕ∞) := by
    rw [heq, Nat.cast_add, ENat.natCast_toNat h1_ne, ENat.natCast_toNat h2_ne]
  exact ⟨I, U, hUE, hmax, Nat.cast_injective hcast⟩

/-- **Edmonds' matroid intersection theorem** (min–max form; [Edmonds1970]; [Schrijver2017],
Theorem 10.9): for matroids `M₁ M₂ : Matroid α` and a finite candidate ground set `E : Finset α`,
the maximum cardinality of a common independent subset of `E` equals the minimum over `U ⊆ E` of
`M₁.eRk ↑U + M₂.eRk ↑(E \ U)`. -/
theorem iSup_card_eq_iInf_eRk_add_eRk (M₁ M₂ : Matroid α) (E : Finset α) :
    ⨆ (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I), (I.card : ℕ∞) =
      ⨅ (U : Finset α) (_ : U ⊆ E), M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  refine le_antisymm (iSup₂_le fun J hJ => le_iInf₂ fun V _ =>
    hJ.2.card_le_eRk_add_eRk hJ.1 V) ?_
  obtain ⟨I, U, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ E
  calc ⨅ (U : Finset α) (_ : U ⊆ E), M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α)
      ≤ M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := iInf₂_le U hUE
    _ = (I.card : ℕ∞) := heq.symm
    _ ≤ ⨆ (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I), (I.card : ℕ∞) :=
      le_iSup₂ (f := fun (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I) => (I.card : ℕ∞))
        I ⟨hmax.1, hmax.2.1⟩

omit [DecidableEq α] in
/-- **Edmonds' matroid intersection theorem** (`Set` min–max form; [Edmonds1970]; [Schrijver2017],
Theorem 10.9): for matroids `M₁ M₂ : Matroid α` and a finite set `X : Set α`, the supremum of
`I.encard` over sets `I ⊆ X` independent in both matroids equals the infimum over `U ⊆ X` of
`M₁.eRk U + M₂.eRk (X \ U)`. Taking `X` to be the common finite ground set of `M₁` and `M₂` gives
the source statement. The proof uses finiteness of `X`; infinite ground sets are not treated. -/
theorem iSup_encard_eq_iInf_eRk_add_eRk (M₁ M₂ : Matroid α) {X : Set α} (hX : X.Finite) :
    ⨆ (I : Set α) (_ : I ⊆ X ∧ M₁.Indep I ∧ M₂.Indep I), I.encard =
      ⨅ (U : Set α) (_ : U ⊆ X), M₁.eRk U + M₂.eRk (X \ U) := by
  classical
  refine le_antisymm (iSup₂_le fun J hJ => le_iInf₂ fun V _ =>
    encard_le_eRk_add_eRk hJ.1 hJ.2.1 hJ.2.2 V) ?_
  obtain ⟨I, U, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ hX.toFinset
  have hUX : (U : Set α) ⊆ X := by
    intro a ha
    exact (Set.Finite.mem_toFinset hX).mp (hUE ha)
  have hIX : (I : Set α) ⊆ X := by
    intro a ha
    exact (Set.Finite.mem_toFinset hX).mp (hmax.1 ha)
  have hsd : X \ (U : Set α) = ((hX.toFinset \ U : Finset α) : Set α) := by
    rw [Finset.coe_sdiff, Set.Finite.coe_toFinset]
  calc ⨅ (U : Set α) (_ : U ⊆ X), M₁.eRk U + M₂.eRk (X \ U)
      ≤ M₁.eRk (U : Set α) + M₂.eRk (X \ (U : Set α)) := iInf₂_le (U : Set α) hUX
    _ = (I : Set α).encard := by rw [hsd, ← heq, Set.encard_coe_eq_coe_finsetCard]
    _ ≤ ⨆ (I : Set α) (_ : I ⊆ X ∧ M₁.Indep I ∧ M₂.Indep I), I.encard :=
      le_iSup₂ (f := fun (I : Set α) (_ : I ⊆ X ∧ M₁.Indep I ∧ M₂.Indep I) => I.encard)
        (I : Set α) ⟨hIX, hmax.2.1.indep_left, hmax.2.1.indep_right⟩

end ExchangeWalkAugmentation

end Cslib.Algorithms.Lean.Matroid
