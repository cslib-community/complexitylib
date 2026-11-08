/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
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

The matroids need not have ground set `E`: elements of `E` outside `Mᵢ.E` are loops of `Mᵢ`, and
`eRk` only depends on the part of a set inside the ground set. Taking `E` to be the common finite
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
  `Cslib.Algorithms.Lean.Matroid.commonIndep_card_le_eRk_add_eRk`,
  `Cslib.Algorithms.Lean.Matroid.commonIndep_card_le_rk_add_rk`: weak duality.
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
theorem commonIndep_card_le_eRk_add_eRk [DecidableEq α] {M₁ M₂ : Matroid α} {E I : Finset α}
    (hIE : I ⊆ E) (hI : IsCommonIndep M₁ M₂ I) (U : Finset α) :
    (I.card : ℕ∞) ≤ M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  rw [← Set.encard_coe_eq_coe_finsetCard, Finset.coe_sdiff]
  exact encard_le_eRk_add_eRk (Finset.coe_subset.mpr hIE) hI.indep_left hI.indep_right _

/-- **Weak duality for matroid intersection** (`ℕ` rank): for any common independent subset `I ⊆ E`
and any `U : Finset α`, `I.card ≤ (M₁.eRk ↑U).toNat + (M₂.eRk ↑(E \ U)).toNat`. -/
theorem commonIndep_card_le_rk_add_rk [DecidableEq α] {M₁ M₂ : Matroid α} {E I : Finset α}
    (hIE : I ⊆ E) (hI : IsCommonIndep M₁ M₂ I) (U : Finset α) :
    I.card ≤ (M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat := by
  have he := commonIndep_card_le_eRk_add_eRk hIE hI U
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
  have hle := commonIndep_card_le_eRk_add_eRk hJE hJ U
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
  let Yset : Finset α := Finset.univ.image y
  let I' : Finset α := (B \ Xset) ∪ Yset
  have hI_indep : M.Indep (I : Set α) :=
    hB_indep.subset (Finset.coe_subset.mpr (Finset.subset_insert y₀ I))
  have hX_sub_B : Xset ⊆ B := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_insert_of_mem (hx_mem i)
  have hdisj_BY : Disjoint B Yset := by
    rw [Finset.disjoint_right]
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hy_not i
  have hdisj_I' : Disjoint (B \ Xset) Yset :=
    hdisj_BY.mono_left Finset.sdiff_subset
  have hX_card : Xset.card = k := by
    rw [Finset.card_image_of_injective _ hx_inj, Finset.card_fin]
  have hY_card : Yset.card = k := by
    rw [Finset.card_image_of_injective _ hy_inj, Finset.card_fin]
  have hI'_card : I'.card = B.card := by
    rw [Finset.card_union_of_disjoint hdisj_I', Finset.card_sdiff_of_subset hX_sub_B,
      hX_card, hY_card]
    exact Nat.sub_add_cancel (hX_card ▸ Finset.card_le_card hX_sub_B)
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
  -- Downward induction on `k - 1 - i` shows every `x i` lies in `M.closure ↑I'`.
  have hx_closure : ∀ d : ℕ, ∀ i : Fin k, k - 1 - i.1 < d → x i ∈ M.closure (I' : Set α) := by
    intro d
    induction d with
    | zero =>
      intro _ hd
      omega
    | succ d ih =>
      intro i hd
      by_cases hlt_d : k - 1 - i.1 < d
      · exact ih i hlt_d
      · have hyi_not_I : y i ∉ (I : Set α) := fun h =>
          hy_not i (Finset.mem_insert_of_mem h)
        have hyi_cl : y i ∈ M.closure (I : Set α) := by
          rw [hI_indep.mem_closure_iff']
          refine ⟨hy_ground i, fun hind => ?_⟩
          exfalso
          apply hy_dep i
          simpa [Finset.coe_insert] using hind
        have hC_circ : M.IsCircuit (M.fundCircuit (y i) (I : Set α)) :=
          hI_indep.fundCircuit_isCircuit hyi_cl hyi_not_I
        have hxi_C : x i ∈ M.fundCircuit (y i) (I : Set α) := by
          rw [hI_indep.mem_fundCircuit_iff hyi_cl hyi_not_I,
            coe_insert_sdiff_singleton_eq hyi_not_I (hx_mem i)]
          exact hdiag i
        have hsub_cl : M.fundCircuit (y i) (I : Set α) \ {x i} ⊆ M.closure (I' : Set α) := by
          intro z ⟨hzC, hzne⟩
          have hz_ins : z ∈ insert (y i) (I : Set α) :=
            M.fundCircuit_subset_insert (y i) (I : Set α) hzC
          rcases Set.mem_insert_iff.mp hz_ins with rfl | hzI
          · exact hmem_cl_I' (y i)
              (Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))
          · by_cases hzX : z ∈ Xset
            · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hzX
              have hri_ne : r ≠ i := fun h => hzne (congrArg x h)
              have hxr_indep : M.Indep ((insert (y i) (I.erase (x r)) : Finset α) : Set α) := by
                have hxr_C : x r ∈ M.fundCircuit (y i) (I : Set α) := hzC
                rwa [hI_indep.mem_fundCircuit_iff hyi_cl hyi_not_I,
                  coe_insert_sdiff_singleton_eq hyi_not_I (hx_mem r)] at hxr_C
              have hnot_lt : ¬ r < i := fun hlt => hno_chord r i hlt hxr_indep
              have hgt : i.1 < r.1 := by
                rcases lt_trichotomy r i with hlt | rfl | hgt
                · exact absurd hlt hnot_lt
                · exact absurd rfl hri_ne
                · exact hgt
              exact ih r (by omega)
            · exact hmem_cl_I' z (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hzI, hzX⟩))
        have hxi_in_cl_C : x i ∈ M.closure (M.fundCircuit (y i) (I : Set α) \ {x i}) :=
          (hC_circ.sdiff_singleton_isBasis hxi_C).subset_closure hxi_C
        exact M.closure_subset_closure_of_subset_closure hsub_cl hxi_in_cl_C
  have hB_sub_cl : (B : Set α) ⊆ M.closure (I' : Set α) := by
    intro a ha
    by_cases haX : a ∈ Xset
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haX
      exact hx_closure k i (by omega)
    · exact hmem_cl_I' a (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, haX⟩))
  have hcard_le_eRk : (I' : Set α).encard ≤ M.eRk (I' : Set α) := by
    rw [Set.encard_coe_eq_coe_finsetCard, hI'_card, ← Set.encard_coe_eq_coe_finsetCard,
      ← hB_indep.eRk_eq_encard, ← M.eRk_closure_eq (I' : Set α)]
    exact M.eRk_mono hB_sub_cl
  exact (M.isRkFinite_of_finite I'.finite_toSet).indep_of_encard_le_eRk hcard_le_eRk

/-- Helper for unreachability duality: if `I : Finset α` is `M`-independent, `S ⊆ I`, `y ∉ I`, and
`M.Indep ↑(insert y S)`, then either `M.Indep ↑(insert y I)` or there exists `x ∈ I \ S` such that
`M.Indep ↑(insert y (I.erase x))`. -/
private theorem indep_insert_or_exists_erase {M : Matroid α} {I S : Finset α} {y : α}
    (hI : M.Indep (I : Set α)) (hSI : S ⊆ I) (hyI : y ∉ I)
    (hyS : M.Indep ((insert y S : Finset α) : Set α)) :
    M.Indep ((insert y I : Finset α) : Set α) ∨
      ∃ x ∈ I \ S, M.Indep ((insert y (I.erase x) : Finset α) : Set α) := by
  have hsub : ((insert y S : Finset α) : Set α) ⊆ ((insert y I : Finset α) : Set α) :=
    Finset.coe_subset.mpr (Finset.insert_subset_insert y hSI)
  obtain ⟨J, hJ_bas, hSJ⟩ := hyS.subset_isBasis'_of_subset hsub
  have hJ_fin : J.Finite :=
    (M.isRkFinite_of_finite (insert y I).finite_toSet).finite_of_isBasis' hJ_bas
  let Jf : Finset α := hJ_fin.toFinset
  have hJf_coe : (Jf : Set α) = J := hJ_fin.coe_toFinset
  have hJf_sub : Jf ⊆ insert y I := by
    rw [← Finset.coe_subset, hJf_coe]
    exact hJ_bas.subset
  have hSJf : insert y S ⊆ Jf := by
    rw [← Finset.coe_subset, hJf_coe]
    exact hSJ
  have hI_le_Jf : I.card ≤ Jf.card := by
    have henc : (I : Set α).encard ≤ (Jf : Set α).encard := by
      rw [← hI.eRk_eq_encard, hJf_coe, ← hJ_bas.eRk_eq_encard]
      exact M.eRk_mono (Finset.coe_subset.mpr (Finset.subset_insert y I))
    simpa [Set.encard_coe_eq_coe_finsetCard] using henc
  have hJf_le : Jf.card ≤ I.card + 1 := by
    calc
      Jf.card ≤ (insert y I).card := Finset.card_le_card hJf_sub
      _ = I.card + 1 := Finset.card_insert_of_notMem hyI
  by_cases hfull : Jf.card = I.card + 1
  · left
    have heq : Jf = insert y I :=
      Finset.eq_of_subset_of_card_le hJf_sub (by rw [Finset.card_insert_of_notMem hyI, hfull])
    rw [← heq, hJf_coe]
    exact hJ_bas.indep
  · right
    have hcard_eq : Jf.card = I.card := by omega
    have hdiff_pos : 0 < (insert y I \ Jf).card := by
      rw [Finset.card_sdiff_of_subset hJf_sub, Finset.card_insert_of_notMem hyI]
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hdiff_pos
    obtain ⟨hx_ins, hx_not_Jf⟩ := Finset.mem_sdiff.mp hx
    have hxy : x ≠ y := fun h => hx_not_Jf (h ▸ hSJf (Finset.mem_insert_self y S))
    have hxI : x ∈ I := by
      rcases Finset.mem_insert.mp hx_ins with rfl | hxI
      · exact absurd rfl hxy
      · exact hxI
    have hx_not_S : x ∉ S := fun hxS =>
      hx_not_Jf (hSJf (Finset.mem_insert_of_mem hxS))
    have hJf_sub_erase : Jf ⊆ insert y (I.erase x) := by
      intro z hz
      rcases Finset.mem_insert.mp (hJf_sub hz) with rfl | hzI
      · exact Finset.mem_insert_self z _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hx_not_Jf (h ▸ hz), hzI⟩)
    have hJf_eq : Jf = insert y (I.erase x) := by
      refine Finset.eq_of_subset_of_card_le hJf_sub_erase ?_
      have hy_not_er : y ∉ I.erase x := fun hy_er => hyI (Finset.mem_of_mem_erase hy_er)
      rw [Finset.card_insert_of_notMem hy_not_er, Finset.card_erase_of_mem hxI, hcard_eq]
      have hx_pos : 1 ≤ I.card := Finset.one_le_card.mpr ⟨x, hxI⟩
      omega
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hxI, hx_not_S⟩, ?_⟩
    rw [← hJf_eq, hJf_coe]
    exact hJ_bas.indep

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
  have hrk1 : M₁.eRk ((E \ R : Finset α) : Set α) = ((I \ R).card : ℕ∞) := by
    have hind : M₁.Indep ((I \ R : Finset α) : Set α) :=
      hI.indep_left.subset (by simp [Finset.coe_sdiff])
    have hsub : ((I \ R : Finset α) : Set α) ⊆ ((E \ R : Finset α) : Set α) :=
      Finset.coe_subset.mpr (Finset.sdiff_subset_sdiff hIE Finset.Subset.rfl)
    have hle : ((I \ R).card : ℕ∞) ≤ M₁.eRk ((E \ R : Finset α) : Set α) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, ← hind.eRk_eq_encard]
      exact M₁.eRk_mono hsub
    refine le_antisymm ?_ hle
    by_contra hnot
    have hlt : M₁.eRk ((I \ R : Finset α) : Set α) < M₁.eRk ((E \ R : Finset α) : Set α) := by
      rw [hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard]
      exact lt_of_not_ge hnot
    obtain ⟨y, ⟨hy_ER, hy_not_IR_set⟩, hy_rk⟩ := M₁.exists_eRk_insert_eq_add_one_of_lt hlt
    obtain ⟨hyE, hy_not_R⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hy_ER)
    have hy_not_IR : y ∉ I \ R := fun h => hy_not_IR_set (Finset.mem_coe.mpr h)
    have hy_not_I : y ∉ I := fun hyI => hy_not_IR (Finset.mem_sdiff.mpr ⟨hyI, hy_not_R⟩)
    have hy_indep_IR : M₁.Indep ((insert y (I \ R) : Finset α) : Set α) := by
      have hfin := (insert y (I \ R)).finite_toSet
      refine (M₁.isRkFinite_of_finite hfin).indep_of_encard_le_eRk ?_
      rw [Finset.coe_insert, hy_rk, hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard,
        ← Finset.coe_insert, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_insert_of_notMem hy_not_IR, Nat.cast_add, Nat.cast_one]
    rcases indep_insert_or_exists_erase hI.indep_left Finset.sdiff_subset hy_not_I hy_indep_IR
      with hfull | ⟨x, hx, hexch⟩
    · exact hy_not_R (hX1 y (Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩) hfull)
    · obtain ⟨hxI, hx_not_IR⟩ := Finset.mem_sdiff.mp hx
      have hxR : x ∈ R := by
        by_contra hxR
        exact hx_not_IR (Finset.mem_sdiff.mpr ⟨hxI, hxR⟩)
      exact hy_not_R (hcl1 x (Finset.mem_inter.mpr ⟨hxR, hxI⟩) y
        (Finset.mem_sdiff.mpr ⟨hyE, hy_not_I⟩) hexch)
  have hrk2 : M₂.eRk (R : Set α) = ((I ∩ R).card : ℕ∞) := by
    have hind : M₂.Indep ((I ∩ R : Finset α) : Set α) :=
      hI.indep_right.subset (by simp [Finset.coe_inter])
    have hsub : ((I ∩ R : Finset α) : Set α) ⊆ (R : Set α) :=
      Finset.coe_subset.mpr Finset.inter_subset_right
    have hle : ((I ∩ R).card : ℕ∞) ≤ M₂.eRk (R : Set α) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, ← hind.eRk_eq_encard]
      exact M₂.eRk_mono hsub
    refine le_antisymm ?_ hle
    by_contra hnot
    have hlt : M₂.eRk ((I ∩ R : Finset α) : Set α) < M₂.eRk (R : Set α) := by
      rw [hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard]
      exact lt_of_not_ge hnot
    obtain ⟨y, ⟨hyR_set, hy_not_IR_set⟩, hy_rk⟩ := M₂.exists_eRk_insert_eq_add_one_of_lt hlt
    have hyR : y ∈ R := Finset.mem_coe.mp hyR_set
    have hy_not_IR : y ∉ I ∩ R := fun h => hy_not_IR_set (Finset.mem_coe.mpr h)
    have hy_not_I : y ∉ I := fun hyI => hy_not_IR (Finset.mem_inter.mpr ⟨hyI, hyR⟩)
    have hy_indep_IR : M₂.Indep ((insert y (I ∩ R) : Finset α) : Set α) := by
      have hfin := (insert y (I ∩ R)).finite_toSet
      refine (M₂.isRkFinite_of_finite hfin).indep_of_encard_le_eRk ?_
      rw [Finset.coe_insert, hy_rk, hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard,
        ← Finset.coe_insert, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_insert_of_notMem hy_not_IR, Nat.cast_add, Nat.cast_one]
    rcases indep_insert_or_exists_erase hI.indep_right Finset.inter_subset_left hy_not_I
        hy_indep_IR with hfull | ⟨x, hx, hexch⟩
    · exact hX2 y (Finset.mem_sdiff.mpr ⟨hyR, hy_not_I⟩) hfull
    · obtain ⟨hxI, hx_not_IR⟩ := Finset.mem_sdiff.mp hx
      have hx_not_R : x ∉ R := fun hxR => hx_not_IR (Finset.mem_inter.mpr ⟨hxI, hxR⟩)
      exact hx_not_R (hcl2 y (Finset.mem_sdiff.mpr ⟨hyR, hy_not_I⟩) x hxI hexch)
  rw [hrk1, hrk2, ← Nat.cast_add, add_comm, Finset.card_inter_add_card_sdiff]

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

theorem IsShortestExchAugWalk.nodup {M₁ M₂ : Matroid α} {E I : Finset α} {p : List α}
    (hshort : IsShortestExchAugWalk M₁ M₂ E I p) : p.Nodup := by
  obtain ⟨hp, hmin⟩ := hshort
  obtain ⟨hne, hX1, hX2, hmemE, hchain⟩ := hp
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  dsimp only at heq
  simp only [Fin.mk.injEq]
  by_contra hne_idx
  wlog hij : i < j generalizing i j
  · exact this j hj i hi heq.symm (Ne.symm hne_idx) (by omega)
  cases i with
  | zero =>
    have hdrop_ne : p.drop j ≠ [] := by
      intro h
      have := List.drop_eq_nil_iff.mp h
      omega
    have haug_drop : IsExchAugWalk M₁ M₂ E I (p.drop j) := by
      refine ⟨hdrop_ne, ?_, ?_, fun z hz => hmemE z (List.mem_of_mem_drop hz), hchain.drop j⟩
      · have hhead : (p.drop j).head hdrop_ne = p.head hne := by
          rw [List.head_drop, ← heq, ← List.head_eq_getElem hne]
        rwa [hhead]
      · rwa [List.getLast_drop]
    have hlen := hmin (p.drop j) haug_drop
    rw [List.length_drop] at hlen
    omega
  | succ i' =>
    have hi' : i' < p.length := by omega
    have harc : IsExchArc M₁ M₂ E I (p[i']'hi') (p[j]'hj) := by
      have h0 : IsExchArc M₁ M₂ E I (p[i']'hi') (p[i' + 1]'hi) :=
        List.IsChain.getElem hchain i' (by omega)
      simpa [heq] using h0
    have haug_sc := isExchAugWalk_take_append_drop ⟨hne, hX1, hX2, hmemE, hchain⟩ hi' hj harc
    have hlen := hmin _ haug_sc
    rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi'),
      List.length_drop] at hlen
    omega

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
  have hnodup : p.Nodup := hshort.nodup
  obtain ⟨hp, hmin⟩ := hshort
  obtain ⟨hne, hX1, hX2, hmemE, hchain⟩ := hp
  have h0_not_I : p.head hne ∉ I := (Finset.mem_sdiff.mp hX1.1).2
  have hlast_not_I : p.getLast hne ∉ I := (Finset.mem_sdiff.mp hX2.1).2
  have hpar := isExchWalk_parity hchain hne h0_not_I
  have hlen_pos : 0 < p.length := List.length_pos_of_ne_nil hne
  have hlast_idx : p.length - 1 < p.length := by omega
  have hlast_even : (p.length - 1) % 2 = 0 := by
    have hget_last : p[p.length - 1]'hlast_idx = p.getLast hne :=
      (List.getLast_eq_getElem hne).symm
    have hnot : ¬ (p.length - 1) % 2 = 1 := fun h1 =>
      hlast_not_I (hget_last ▸ (hpar (p.length - 1) hlast_idx).mpr h1)
    omega
  let k : ℕ := (p.length - 1) / 2
  have hlen_eq : p.length = 2 * k + 1 := by omega
  let I' : Finset α := I ∆ p.toFinset
  have hI'_sub_E : I' ⊆ E := by
    intro a ha
    rw [mem_symmDiff_toFinset] at ha
    by_cases hap : a ∈ p
    · exact hmemE a hap
    · exact hIE (ha.mpr hap)
  -- Forward indexing for `M₁`: `y₀ = p[0]`, `x i = p[2i+1]`, `y i = p[2i+2]`.
  let y₀ : α := p[0]'hlen_pos
  let x : Fin k → α := fun i => p[2 * i.1 + 1]'(by omega)
  let y : Fin k → α := fun i => p[2 * i.1 + 2]'(by omega)
  have hy₀_eq_head : y₀ = p.head hne := (List.head_eq_getElem hne).symm
  have hy₀_not : y₀ ∉ I := hy₀_eq_head ▸ h0_not_I
  have hB₁_indep : M₁.Indep ((insert y₀ I : Finset α) : Set α) := hy₀_eq_head ▸ hX1.2
  have hx_mem : ∀ i : Fin k, x i ∈ I := fun i =>
    (hpar (2 * i.1 + 1) (by omega)).mpr (by omega)
  have hx_inj : Function.Injective x := by
    intro i j hij
    have heq := (List.Nodup.getElem_inj_iff hnodup).mp hij
    exact Fin.ext (by omega)
  have hy_not : ∀ i : Fin k, y i ∉ insert y₀ I := by
    intro i hmem
    rcases Finset.mem_insert.mp hmem with heq | hyI
    · have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
      omega
    · have := (hpar (2 * i.1 + 2) (by omega)).mp hyI
      omega
  have hy_inj : Function.Injective y := by
    intro i j hij
    have heq := (List.Nodup.getElem_inj_iff hnodup).mp hij
    exact Fin.ext (by omega)
  have hy_dep₁ : ∀ i : Fin k, ¬ M₁.Indep ((insert (y i) I : Finset α) : Set α) := by
    intro i hind
    let idx := 2 * i.1 + 2
    have hidx : idx < p.length := by omega
    have hdrop_ne : p.drop idx ≠ [] := by
      intro h
      have := List.drop_eq_nil_iff.mp h
      omega
    have hyi_not_I : y i ∉ I := fun h => by
      have := (hpar idx hidx).mp h
      omega
    have hyi_E : y i ∈ E := hmemE (y i) (List.getElem_mem hidx)
    have haug_drop : IsExchAugWalk M₁ M₂ E I (p.drop idx) := by
      refine ⟨hdrop_ne, ?_, ?_, fun z hz => hmemE z (List.mem_of_mem_drop hz), hchain.drop idx⟩
      · rw [List.head_drop]
        exact ⟨Finset.mem_sdiff.mpr ⟨hyi_E, hyi_not_I⟩, hind⟩
      · rwa [List.getLast_drop]
    have hlen := hmin (p.drop idx) haug_drop
    rw [List.length_drop] at hlen
    omega
  have hdiag₁ : ∀ i : Fin k, M₁.Indep ((insert (y i) (I.erase (x i)) : Finset α) : Set α) := by
    intro i
    have harc : IsExchArc M₁ M₂ E I (x i) (y i) :=
      List.IsChain.getElem hchain (2 * i.1 + 1) (by omega)
    rcases harc with ⟨_, _, hind⟩ | ⟨hx_not_I, _, _⟩
    · exact hind
    · exact absurd (hx_mem i) (Finset.mem_sdiff.mp hx_not_I).2
  have hno_chord₁ : ∀ i j : Fin k, i < j →
      ¬ M₁.Indep ((insert (y j) (I.erase (x i)) : Finset α) : Set α) := by
    intro i j hij hind
    have hyj_not_I : y j ∉ I := fun h => hy_not j (Finset.mem_insert_of_mem h)
    have hyj_E : y j ∈ E := hmemE (y j) (List.getElem_mem (by omega))
    have harc : IsExchArc M₁ M₂ E I (x i) (y j) :=
      .inl ⟨hx_mem i, Finset.mem_sdiff.mpr ⟨hyj_E, hyj_not_I⟩, hind⟩
    have haug_sc := isExchAugWalk_take_append_drop ⟨hne, hX1, hX2, hmemE, hchain⟩
      (i := 2 * i.1 + 1) (j := 2 * j.1 + 2) (by omega) (by omega) harc
    have hlen := hmin _ haug_sc
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega), List.length_drop] at hlen
    have hij_val : i.1 < j.1 := hij
    omega
  have hI'_eq₁ : I' = (insert y₀ I \ Finset.univ.image x) ∪ Finset.univ.image y := by
    ext a
    rw [mem_symmDiff_toFinset]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and]
    by_cases hap : a ∈ p
    · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hap
      have hmem_t : p[t]'ht ∈ p := List.getElem_mem ht
      by_cases hodd : t % 2 = 1
      · have hinI : p[t]'ht ∈ I := (hpar t ht).mpr hodd
        let idx : Fin k := ⟨t / 2, by omega⟩
        have hx_eq : x idx = p[t]'ht := by
          simp only [x, idx]
          congr 1
          omega
        have hnot_y : ¬ ∃ i : Fin k, y i = p[t]'ht := by
          rintro ⟨i, hi⟩
          have := (List.Nodup.getElem_inj_iff hnodup).mp hi
          omega
        exact ⟨fun h => ((h.mp hinI) hmem_t).elim,
          fun h => by
            rcases h with ⟨_, hnot_x⟩ | hy_ex
            · exact absurd ⟨idx, hx_eq⟩ hnot_x
            · exact absurd hy_ex hnot_y⟩
      · have hnotI : p[t]'ht ∉ I := fun h => hodd ((hpar t ht).mp h)
        have hnot_x : ¬ ∃ i : Fin k, x i = p[t]'ht := by
          rintro ⟨i, hi⟩
          have := (List.Nodup.getElem_inj_iff hnodup).mp hi
          omega
        refine ⟨fun _ => ?_, fun _ => ⟨fun h => absurd h hnotI, fun h => absurd hmem_t h⟩⟩
        by_cases ht0 : t = 0
        · left
          refine ⟨.inl ?_, hnot_x⟩
          simp only [y₀]
          congr 1
        · right
          refine ⟨⟨(t - 2) / 2, by omega⟩, ?_⟩
          simp only [y]
          congr 1
          omega
    · have hne_y₀ : a ≠ y₀ := fun h => hap (h ▸ List.getElem_mem hlen_pos)
      have hnot_x : ¬ ∃ i : Fin k, x i = a := by
        rintro ⟨i, rfl⟩
        exact hap (List.getElem_mem (by omega))
      have hnot_y : ¬ ∃ i : Fin k, y i = a := by
        rintro ⟨i, rfl⟩
        exact hap (List.getElem_mem (by omega))
      simp [hap, hne_y₀, hnot_x, hnot_y]
  have hind₁ : M₁.Indep (I' : Set α) := by
    rw [hI'_eq₁]
    exact indep_exchange_chain hB₁_indep hx_mem hx_inj hy_not hy_inj hy_dep₁ hdiag₁
      hno_chord₁
  -- Reverse indexing for `M₂`: `y₀' = p[2k]`, `x' i = p[2(k-1-i)+1]`, `y' i = p[2(k-1-i)]`.
  let y₀' : α := p[2 * k]'(by omega)
  let x' : Fin k → α := fun i => p[2 * (k - 1 - i.1) + 1]'(by omega)
  let y' : Fin k → α := fun i => p[2 * (k - 1 - i.1)]'(by omega)
  have hy₀'_eq_last : y₀' = p.getLast hne := by
    rw [List.getLast_eq_getElem]
    simp only [y₀']
    congr 1
    omega
  have hy₀'_not : y₀' ∉ I := hy₀'_eq_last ▸ hlast_not_I
  have hB₂_indep : M₂.Indep ((insert y₀' I : Finset α) : Set α) := hy₀'_eq_last ▸ hX2.2
  have hx'_mem : ∀ i : Fin k, x' i ∈ I := fun i =>
    (hpar (2 * (k - 1 - i.1) + 1) (by omega)).mpr (by omega)
  have hx'_inj : Function.Injective x' := by
    intro i j hij
    have heq := (List.Nodup.getElem_inj_iff hnodup).mp hij
    exact Fin.ext (by omega)
  have hy'_not : ∀ i : Fin k, y' i ∉ insert y₀' I := by
    intro i hmem
    rcases Finset.mem_insert.mp hmem with heq | hyI
    · have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
      omega
    · have := (hpar (2 * (k - 1 - i.1)) (by omega)).mp hyI
      omega
  have hy'_inj : Function.Injective y' := by
    intro i j hij
    have heq := (List.Nodup.getElem_inj_iff hnodup).mp hij
    exact Fin.ext (by omega)
  have hy'_dep₂ : ∀ i : Fin k, ¬ M₂.Indep ((insert (y' i) I : Finset α) : Set α) := by
    intro i hind
    let idx := 2 * (k - 1 - i.1)
    have hidx : idx < p.length := by omega
    have htake_ne : p.take (idx + 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp [Nat.min_eq_left (Nat.succ_le_of_lt hidx)] at hlen
    have hyi_not_I : y' i ∉ I := fun h => by
      have := (hpar idx hidx).mp h
      omega
    have hyi_E : y' i ∈ E := hmemE (y' i) (List.getElem_mem hidx)
    have haug_take : IsExchAugWalk M₁ M₂ E I (p.take (idx + 1)) := by
      refine ⟨htake_ne, ?_, ?_, fun z hz => hmemE z (List.mem_of_mem_take hz), hchain.take _⟩
      · rwa [List.head_take]
      · have hlast : (p.take (idx + 1)).getLast htake_ne = y' i := by
          rw [List.getLast_eq_getElem]
          simp [y', idx, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hidx)]
        rw [hlast]
        exact ⟨Finset.mem_sdiff.mpr ⟨hyi_E, hyi_not_I⟩, hind⟩
    have hlen := hmin (p.take (idx + 1)) haug_take
    rw [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hidx)] at hlen
    omega
  have hdiag₂ : ∀ i : Fin k, M₂.Indep ((insert (y' i) (I.erase (x' i)) : Finset α) : Set α) := by
    intro i
    have harc : IsExchArc M₁ M₂ E I (y' i) (x' i) :=
      List.IsChain.getElem hchain (2 * (k - 1 - i.1)) (by omega)
    rcases harc with ⟨hy_in_I, _, _⟩ | ⟨_, _, hind⟩
    · exact absurd hy_in_I (fun h => hy'_not i (Finset.mem_insert_of_mem h))
    · exact hind
  have hno_chord₂ : ∀ i j : Fin k, i < j →
      ¬ M₂.Indep ((insert (y' j) (I.erase (x' i)) : Finset α) : Set α) := by
    intro i j hij hind
    have hyj_not_I : y' j ∉ I := fun h => hy'_not j (Finset.mem_insert_of_mem h)
    have hyj_E : y' j ∈ E := hmemE (y' j) (List.getElem_mem (by omega))
    have harc : IsExchArc M₁ M₂ E I (y' j) (x' i) :=
      .inr ⟨Finset.mem_sdiff.mpr ⟨hyj_E, hyj_not_I⟩, hx'_mem i, hind⟩
    have hij_val : i.1 < j.1 := hij
    have haug_sc := isExchAugWalk_take_append_drop ⟨hne, hX1, hX2, hmemE, hchain⟩
      (i := 2 * (k - 1 - j.1)) (j := 2 * (k - 1 - i.1) + 1) (by omega) (by omega) harc
    have hlen := hmin _ haug_sc
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega), List.length_drop] at hlen
    omega
  have hI'_eq₂ : I' = (insert y₀' I \ Finset.univ.image x') ∪ Finset.univ.image y' := by
    ext a
    rw [mem_symmDiff_toFinset]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and]
    by_cases hap : a ∈ p
    · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hap
      have hmem_t : p[t]'ht ∈ p := List.getElem_mem ht
      by_cases hodd : t % 2 = 1
      · have hinI : p[t]'ht ∈ I := (hpar t ht).mpr hodd
        let idx : Fin k := ⟨k - 1 - t / 2, by omega⟩
        have hx_eq : x' idx = p[t]'ht := by
          simp only [x', idx]
          congr 1
          omega
        have hnot_y : ¬ ∃ i : Fin k, y' i = p[t]'ht := by
          rintro ⟨i, hi⟩
          have := (List.Nodup.getElem_inj_iff hnodup).mp hi
          omega
        exact ⟨fun h => ((h.mp hinI) hmem_t).elim,
          fun h => by
            rcases h with ⟨_, hnot_x⟩ | hy_ex
            · exact absurd ⟨idx, hx_eq⟩ hnot_x
            · exact absurd hy_ex hnot_y⟩
      · have hnotI : p[t]'ht ∉ I := fun h => hodd ((hpar t ht).mp h)
        have hnot_x : ¬ ∃ i : Fin k, x' i = p[t]'ht := by
          rintro ⟨i, hi⟩
          have := (List.Nodup.getElem_inj_iff hnodup).mp hi
          omega
        refine ⟨fun _ => ?_, fun _ => ⟨fun h => absurd h hnotI, fun h => absurd hmem_t h⟩⟩
        by_cases htk : t = 2 * k
        · left
          refine ⟨.inl ?_, hnot_x⟩
          simp only [y₀']
          congr 1
        · right
          refine ⟨⟨k - 1 - t / 2, by omega⟩, ?_⟩
          simp only [y']
          congr 1
          omega
    · have hne_y₀' : a ≠ y₀' := fun h => hap (h ▸ List.getElem_mem (by omega))
      have hnot_x : ¬ ∃ i : Fin k, x' i = a := by
        rintro ⟨i, rfl⟩
        exact hap (List.getElem_mem (by omega))
      have hnot_y : ¬ ∃ i : Fin k, y' i = a := by
        rintro ⟨i, rfl⟩
        exact hap (List.getElem_mem (by omega))
      simp [hap, hne_y₀', hnot_x, hnot_y]
  have hind₂ : M₂.Indep (I' : Set α) := by
    rw [hI'_eq₂]
    exact indep_exchange_chain hB₂_indep hx'_mem hx'_inj hy'_not hy'_inj hy'_dep₂ hdiag₂
      hno_chord₂
  -- Cardinality `I'.card = I.card + 1`.
  have hcard : I'.card = I.card + 1 := by
    rw [hI'_eq₁]
    have hX_sub : Finset.univ.image x ⊆ insert y₀ I := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_insert_of_mem (hx_mem i)
    have hdisj : Disjoint (insert y₀ I \ Finset.univ.image x) (Finset.univ.image y) := by
      rw [Finset.disjoint_right]
      intro a ha hmem
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hy_not i (Finset.mem_sdiff.mp hmem).1
    have hX_card : (Finset.univ.image x).card = k := by
      rw [Finset.card_image_of_injective _ hx_inj, Finset.card_fin]
    have hY_card : (Finset.univ.image y).card = k := by
      rw [Finset.card_image_of_injective _ hy_inj, Finset.card_fin]
    have hB_card : (insert y₀ I).card = I.card + 1 := Finset.card_insert_of_notMem hy₀_not
    have hk_le : k ≤ I.card + 1 := by
      rw [← hX_card, ← hB_card]
      exact Finset.card_le_card hX_sub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hX_sub,
      hB_card, hX_card, hY_card]
    omega
  exact ⟨hI'_sub_E, ⟨hind₁, hind₂⟩, hcard⟩

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
(`commonIndep_card_le_eRk_add_eRk`), the maximum equals the minimum; see
`iSup_card_eq_iInf_eRk_add_eRk`. The proof is the augmenting-path algorithm: start from `∅`,
augment along shortest exchange walks (`IsShortestExchAugWalk.augment`) until none exists, then
read off `U` (`exists_separator_of_not_exists_exchAugWalk`). -/
theorem exists_commonIndep_card_eq_eRk_add_eRk (M₁ M₂ : Matroid α) (E : Finset α) :
    ∃ I U : Finset α, I ⊆ E ∧ U ⊆ E ∧ IsMaxCommonIndep M₁ M₂ E I ∧
      (I.card : ℕ∞) = M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) :=
  exists_commonIndep_card_eq_aux M₁ M₂ E E.card ∅ (Finset.empty_subset E)
    (isCommonIndep_empty M₁ M₂) (by simp)

/-- **Edmonds' matroid intersection theorem** (`ℕ` rank form): some maximum common independent
subset `I ⊆ E` and some `U ⊆ E` satisfy `I.card = (M₁.eRk ↑U).toNat + (M₂.eRk ↑(E \ U)).toNat`.
The ranks are finite because `E` is. -/
theorem exists_commonIndep_card_eq_rk_add_rk (M₁ M₂ : Matroid α) (E : Finset α) :
    ∃ I U : Finset α, I ⊆ E ∧ U ⊆ E ∧ IsMaxCommonIndep M₁ M₂ E I ∧
      I.card = (M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat := by
  obtain ⟨I, U, hIE, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ E
  have h1_ne : M₁.eRk (U : Set α) ≠ ⊤ :=
    (M₁.isRkFinite_of_finite U.finite_toSet).eRk_lt_top.ne
  have h2_ne : M₂.eRk ((E \ U : Finset α) : Set α) ≠ ⊤ :=
    (M₂.isRkFinite_of_finite (E \ U).finite_toSet).eRk_lt_top.ne
  have hcast : (I.card : ℕ∞) =
      (((M₁.eRk (U : Set α)).toNat + (M₂.eRk ((E \ U : Finset α) : Set α)).toNat : ℕ) : ℕ∞) := by
    rw [heq, Nat.cast_add, ENat.natCast_toNat h1_ne, ENat.natCast_toNat h2_ne]
  exact ⟨I, U, hIE, hUE, hmax, Nat.cast_injective hcast⟩

/-- **Edmonds' matroid intersection theorem** (min–max form; [Edmonds1970]; [Schrijver2017],
Theorem 10.9): for matroids `M₁ M₂ : Matroid α` and a finite candidate ground set `E : Finset α`,
the maximum cardinality of a common independent subset of `E` equals the minimum over `U ⊆ E` of
`M₁.eRk ↑U + M₂.eRk ↑(E \ U)`. -/
theorem iSup_card_eq_iInf_eRk_add_eRk (M₁ M₂ : Matroid α) (E : Finset α) :
    ⨆ (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I), (I.card : ℕ∞) =
      ⨅ (U : Finset α) (_ : U ⊆ E), M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := by
  refine le_antisymm (iSup₂_le fun J hJ => le_iInf₂ fun V _ =>
    commonIndep_card_le_eRk_add_eRk hJ.1 hJ.2 V) ?_
  obtain ⟨I, U, hIE, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ E
  calc ⨅ (U : Finset α) (_ : U ⊆ E), M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α)
      ≤ M₁.eRk (U : Set α) + M₂.eRk ((E \ U : Finset α) : Set α) := iInf₂_le U hUE
    _ = (I.card : ℕ∞) := heq.symm
    _ ≤ ⨆ (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I), (I.card : ℕ∞) :=
      le_iSup₂ (f := fun (I : Finset α) (_ : I ⊆ E ∧ IsCommonIndep M₁ M₂ I) => (I.card : ℕ∞))
        I ⟨hIE, hmax.2.1⟩

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
  obtain ⟨I, U, hIE, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk M₁ M₂ hX.toFinset
  have hUX : (U : Set α) ⊆ X := by
    intro a ha
    exact (Set.Finite.mem_toFinset hX).mp (hUE ha)
  have hIX : (I : Set α) ⊆ X := by
    intro a ha
    exact (Set.Finite.mem_toFinset hX).mp (hIE ha)
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
