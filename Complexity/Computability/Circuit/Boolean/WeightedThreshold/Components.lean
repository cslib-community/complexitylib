/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Cut
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Input-support components, fan-in-two splits, and block-excess bounds

This module proves two structural lower bounds for weighted threshold programs from the
coordinate-split and median-cut rectangle lemmas in `Cut.lean`:

* **C5 (`lt_of_inputSupport_card_le_two`, `circuit_lt_of_inputSupport_card_le_two`)**: when every
  gate has aggregated input support of size at most `2`, the input-support graph on `Fin n` has at
  least `n - |inputGates p|` connected components that are trees (`|V| = |E| + 1`). Grouping `L`
  such components into `U` produces a coordinate split crossed by no gate with excess `L`, yielding
  `n < (inputGates p).card + 2 * L` for any two-sided `K`-rectangle-free function with `K ≤ 2 ^ L`.
* **C6 (`lt_of_blocks`, `circuit_lt_of_blocks`)**: given a set `F` of freely-read inputs and a
  pairwise disjoint block partition `𝓑` of `Fᶜ` such that every gate's residual support outside
  `F` lies in a single block of `𝓑` and every block has excess `|b| - e_b ≤ M`, a subset-sum split
  (`exists_subset_sum_ge`) and `exists_rectangle_of_cut_with_fixed` yield
  `n < F.card + (inputGates p).card + M + 2 * k`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.supportGraph`: the graph on `Fin n` where two inputs
  are adjacent when some gate has nonzero aggregated weight on both.
* `Cslib.Circuits.Boolean.WeightedThreshold.componentInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.componentGates`: the inputs and active gates in a
  connected component of `supportGraph p`.
* `Cslib.Circuits.Boolean.WeightedThreshold.residualGates`: gates whose residual input support
  outside `F` is nonempty and contained in a block `b`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.sum_card_componentInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.sum_card_componentGates`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_componentInputs_le`: component counting for
  fan-in-two input supports.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_split_of_inputSupport_card_le_two`: unsplit
  coordinate cut with prescribed excess `L`.
* `Cslib.Circuits.Boolean.WeightedThreshold.lt_of_inputSupport_card_le_two`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_inputSupport_card_le_two`: the C5
  fan-in-two component lower bound.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_subset_sum_ge`: balanced subset-sum partition
  for bounded weights.
* `Cslib.Circuits.Boolean.WeightedThreshold.lt_of_blocks`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_blocks`: the C6 block-excess lower bound.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*,
  Threshold/Internal/Components, SplitBound, and Excess][Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-! ### Input-support graph and connected components -/

open Classical in
/-- The input-support graph of a weighted threshold program: two inputs are adjacent when some
gate has nonzero aggregated weight on both. -/
def supportGraph (p : Program signature n g) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ j, u ∈ inputSupport p j ∧ v ∈ inputSupport p j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.2, h.2.choose_spec.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- The inputs belonging to a connected component of `supportGraph p`. -/
noncomputable def componentInputs (p : Program signature n g)
    (c : (supportGraph p).ConnectedComponent) : Finset (Fin n) :=
  univ.filter fun u => (supportGraph p).connectedComponentMk u = c

open Classical in
/-- The gates with nonempty aggregated input support inside a connected component of
`supportGraph p`. -/
noncomputable def componentGates (p : Program signature n g)
    (c : (supportGraph p).ConnectedComponent) : Finset (Fin g) :=
  univ.filter fun j => inputSupport p j ≠ ∅ ∧ inputSupport p j ⊆ componentInputs p c

section Components

variable (p : Program signature n g)

/-- An input `u` belongs to `componentInputs p c` if and only if its connected component in
`supportGraph p` is `c`. -/
@[simp]
theorem mem_componentInputs {c : (supportGraph p).ConnectedComponent} {u : Fin n} :
    u ∈ componentInputs p c ↔ (supportGraph p).connectedComponentMk u = c := by
  classical
  simp [componentInputs]

/-- Coercing `componentInputs p c` to a set yields the support `c.supp` of the connected component
`c`. -/
theorem coe_componentInputs (c : (supportGraph p).ConnectedComponent) :
    (componentInputs p c : Set (Fin n)) = c.supp := by
  ext u
  simp [mem_componentInputs, SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- A gate belongs to `componentGates p c` if and only if its input support is nonempty and
contained in `componentInputs p c`. -/
@[simp]
theorem mem_componentGates {c : (supportGraph p).ConnectedComponent} {j : Fin g} :
    j ∈ componentGates p c ↔ inputSupport p j ≠ ∅ ∧ inputSupport p j ⊆ componentInputs p c := by
  classical
  simp [componentGates]

/-- The input support of a gate lies in the connected component of any of its inputs. -/
theorem inputSupport_subset_componentInputs {j : Fin g} {u : Fin n}
    (hu : u ∈ inputSupport p j) :
    inputSupport p j ⊆ componentInputs p ((supportGraph p).connectedComponentMk u) := by
  intro v hv
  rw [mem_componentInputs]
  by_cases huv : v = u
  · rw [huv]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨huv, j, hv, hu⟩

open Classical in
/-- The connected components of `supportGraph p` partition the `n` inputs. -/
theorem sum_card_componentInputs : ∑ c, (componentInputs p c).card = n := by
  have h := card_eq_sum_card_fiberwise (f := (supportGraph p).connectedComponentMk)
    (s := univ) (t := univ) (fun _ _ => mem_univ _)
  simpa [componentInputs] using h.symm

open Classical in
private theorem pairwiseDisjoint_componentInputs :
    ((univ : Finset (supportGraph p).ConnectedComponent) : Set _).PairwiseDisjoint
      (componentInputs p) := by
  intro c _ c' _ hcc'
  rw [Function.onFun, disjoint_left]
  intro u hu hu'
  rw [mem_componentInputs] at hu hu'
  exact hcc' (hu.symm.trans hu')

open Classical in
private theorem pairwiseDisjoint_componentGates :
    ((univ : Finset (supportGraph p).ConnectedComponent) : Set _).PairwiseDisjoint
      (componentGates p) := by
  intro c _ c' _ hcc'
  rw [Function.onFun, disjoint_left]
  intro j hj hj'
  rw [mem_componentGates] at hj hj'
  obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hj.1
  have h1 := (mem_componentInputs p).mp (hj.2 hu)
  have h2 := (mem_componentInputs p).mp (hj'.2 hu)
  exact hcc' (h1.symm.trans h2)

open Classical in
/-- The input-reading gates are partitioned by the connected components of `supportGraph p`. -/
private theorem inputGates_eq_biUnion_componentGates :
    inputGates p = univ.biUnion (componentGates p) := by
  ext j
  simp only [mem_biUnion, mem_univ, true_and, mem_componentGates, ← inputSupport_ne_empty_iff]
  constructor
  · intro hj
    obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hj
    exact ⟨_, hj, inputSupport_subset_componentInputs p hu⟩
  · rintro ⟨_, hj, -⟩
    exact hj

open Classical in
/-- The sizes of `componentGates p c` sum to `(inputGates p).card`. -/
theorem sum_card_componentGates :
    ∑ c, (componentGates p c).card = (inputGates p).card := by
  rw [inputGates_eq_biUnion_componentGates, card_biUnion (pairwiseDisjoint_componentGates p)]

private theorem exists_gate_of_edge (h2 : ∀ j, (inputSupport p j).card ≤ 2)
    (c : (supportGraph p).ConnectedComponent) (e : Sym2 c.supp)
    (he : e ∈ c.toSimpleGraph.edgeSet) :
    ∃ j ∈ componentGates p c, ∀ u, u ∈ inputSupport p j ↔ u ∈ e.map Subtype.val := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨hne, j, ha, hb⟩ : (supportGraph p).Adj a.1 b.1 := he
    have hab : ({a.1, b.1} : Finset (Fin n)) = inputSupport p j := by
      apply eq_of_subset_of_card_le
      · intro u hu
        rw [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      · rw [card_pair hne]
        exact h2 j
    refine ⟨j, ?_, fun u => ?_⟩
    · rw [mem_componentGates]
      refine ⟨nonempty_iff_ne_empty.mp ⟨_, ha⟩, fun u hu => ?_⟩
      rw [← hab, mem_insert, mem_singleton] at hu
      rw [mem_componentInputs]
      rcases hu with rfl | rfl
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp a.2
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp b.2
    · rw [← hab, Sym2.map_mk, mem_insert, mem_singleton, Sym2.mem_iff]

/-- When every gate has aggregated input support of size at most `2`, every connected component
of `supportGraph p` has at most one more input than active gates. -/
theorem card_componentInputs_le (h2 : ∀ j, (inputSupport p j).card ≤ 2)
    (c : (supportGraph p).ConnectedComponent) :
    (componentInputs p c).card ≤ (componentGates p c).card + 1 := by
  have h1 : Nat.card c.supp ≤ Nat.card c.toSimpleGraph.edgeSet + 1 :=
    c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card c.supp = (componentInputs p c).card := by
    rw [← coe_componentInputs]
    exact Nat.card_eq_finsetCard _
  have hE : Nat.card c.toSimpleGraph.edgeSet ≤ (componentGates p c).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨(exists_gate_of_edge p h2 c e.1 e.2).choose,
        (exists_gate_of_edge p h2 c e.1 e.2).choose_spec.1⟩) ?_
    intro e e' hee'
    have hj := (exists_gate_of_edge p h2 c e.1 e.2).choose_spec.2
    have hj' := (exists_gate_of_edge p h2 c e'.1 e'.2).choose_spec.2
    have heq : (exists_gate_of_edge p h2 c e.1 e.2).choose =
        (exists_gate_of_edge p h2 c e'.1 e'.2).choose := congrArg Subtype.val hee'
    rw [heq] at hj
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    apply Sym2.ext
    intro u
    exact (hj u).symm.trans (hj' u)
  omega

end Components

/-! ### C5: Fan-in-two component split and lower bound -/

/-- When every gate of `p` has aggregated input support of size at most `2`, for every
`L ≤ n - (inputGates p).card` there is a coordinate split `U` that no gate crosses and whose
size exceeds the number of active gates on `U` by `L`. -/
theorem exists_split_of_inputSupport_card_le_two (p : Program signature n g)
    (h2 : ∀ j, (inputSupport p j).card ≤ 2) (L : ℕ) (hL : L + (inputGates p).card ≤ n) :
    ∃ U : Finset (Fin n), (∀ j, inputSupport p j ⊆ U ∨ inputSupport p j ⊆ Uᶜ) ∧
      U.card = (univ.filter fun j => inputSupport p j ⊆ U ∧ inputSupport p j ≠ ∅).card + L := by
  classical
  have hT : L ≤ (univ.filter fun c : (supportGraph p).ConnectedComponent =>
      (componentInputs p c).card = (componentGates p c).card + 1).card := by
    have h1 : ∀ c ∈ (univ : Finset (supportGraph p).ConnectedComponent),
        (componentInputs p c).card ≤ (componentGates p c).card +
          if (componentInputs p c).card = (componentGates p c).card + 1 then 1 else 0 := by
      intro c _
      have := card_componentInputs_le p h2 c
      split_ifs <;> omega
    have hsum := sum_le_sum h1
    rw [sum_add_distrib, sum_boole, sum_card_componentInputs,
      sum_card_componentGates, Nat.cast_id] at hsum
    omega
  obtain ⟨𝒯, h𝒯, hcard⟩ := exists_subset_card_eq hT
  refine ⟨𝒯.biUnion (componentInputs p), fun j => ?_, ?_⟩
  · by_cases hj : inputSupport p j = ∅
    · left
      rw [hj]
      exact empty_subset _
    obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hj
    have hsub := inputSupport_subset_componentInputs p hu
    by_cases hc : (supportGraph p).connectedComponentMk u ∈ 𝒯
    · left
      exact hsub.trans (subset_biUnion_of_mem (componentInputs p) hc)
    · right
      intro v hv
      rw [mem_compl, mem_biUnion]
      rintro ⟨c, hc𝒯, hvc⟩
      have h1 := (mem_componentInputs p).mp (hsub hv)
      have h2 := (mem_componentInputs p).mp hvc
      apply hc
      rw [h1.symm.trans h2]
      exact hc𝒯
  · have hdisjI : (𝒯 : Set (supportGraph p).ConnectedComponent).PairwiseDisjoint
        (componentInputs p) :=
      (pairwiseDisjoint_componentInputs p).subset (coe_subset.mpr (subset_univ _))
    have hdisjG : (𝒯 : Set (supportGraph p).ConnectedComponent).PairwiseDisjoint
        (componentGates p) :=
      (pairwiseDisjoint_componentGates p).subset (coe_subset.mpr (subset_univ _))
    have hfilter : (univ.filter fun j =>
        inputSupport p j ⊆ 𝒯.biUnion (componentInputs p) ∧ inputSupport p j ≠ ∅) =
          𝒯.biUnion (componentGates p) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_componentGates]
      constructor
      · rintro ⟨hsub, hne⟩
        obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hne
        obtain ⟨c, hc, huc⟩ := mem_biUnion.mp (hsub hu)
        rw [mem_componentInputs] at huc
        refine ⟨c, hc, hne, ?_⟩
        rw [← huc]
        exact inputSupport_subset_componentInputs p hu
      · rintro ⟨c, hc, hne, hsub⟩
        exact ⟨hsub.trans (subset_biUnion_of_mem _ hc), hne⟩
    have htree : ∀ c ∈ 𝒯, (componentInputs p c).card = (componentGates p c).card + 1 :=
      fun c hc => (mem_filter.mp (h𝒯 hc)).2
    rw [hfilter, card_biUnion hdisjI, card_biUnion hdisjG,
      sum_congr rfl htree, sum_add_distrib, sum_const, smul_eq_mul, mul_one, hcard]

private theorem card_filter_subset_add_card_filter_subset_compl_le
    (p : Program signature n g) (U : Finset (Fin n)) :
    (univ.filter fun j => inputSupport p j ⊆ U ∧ ¬ inputSupport p j ⊆ ∅).card +
      (univ.filter fun j => inputSupport p j ⊆ Uᶜ ∧ ¬ inputSupport p j ⊆ ∅).card ≤
        (inputGates p).card := by
  classical
  rw [← card_union_of_disjoint]
  · apply card_le_card
    intro j hj
    simp only [mem_union, mem_filter, mem_univ, true_and, subset_empty] at hj
    rw [← inputSupport_ne_empty_iff]
    rcases hj with h | h <;> exact h.2
  · rw [disjoint_filter]
    intro j _ h h'
    apply h.2
    intro i hi
    exact (mem_compl.mp (h'.1 hi) (h.1 hi)).elim

/-- **C5: component bound for input fan-in two.** If every gate of `p` has aggregated input
support of size at most `2` and `p` computes a two-sided `K`-rectangle-free function `f` through
`readout` with `K ≤ 2 ^ L`, then `n < (inputGates p).card + 2 * L`. -/
theorem lt_of_inputSupport_card_le_two (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (h2 : ∀ j, (inputSupport p j).card ≤ 2) {L : ℕ} (hK : K ≤ 2 ^ L) :
    n < (inputGates p).card + 2 * L := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨U, hsplit, hU⟩ := exists_split_of_inputSupport_card_le_two p h2 L (by omega)
  obtain ⟨P, Q, b, hb, hP, hQ⟩ :=
    exists_rectangle_of_split p readout hreadout U ∅ ∅ (empty_subset _) (empty_subset _) hsplit
  have hsum := card_filter_subset_add_card_filter_subset_compl_le p U
  set gU := (univ.filter fun j => inputSupport p j ⊆ U ∧ ¬ inputSupport p j ⊆ ∅).card with hgU
  set gV := (univ.filter fun j => inputSupport p j ⊆ Uᶜ ∧ ¬ inputSupport p j ⊆ ∅).card with hgV
  have hU' : U.card = gU + L := by
    rw [hU, hgU]
    congr 2
    ext j
    simp [subset_empty]
  have hcompl : Uᶜ.card = n - U.card := by
    rw [card_compl, Fintype.card_fin]
  simp only [card_empty, Nat.sub_zero] at hP hQ
  have hPK : K ≤ P.card := le_card_of_pow_le hP (by omega) hK
  have hQK : K ≤ Q.card := le_card_of_pow_le hQ (by omega) hK
  rcases card_lt_or_card_lt_of_rectangleFree hf U P Q b hb with h | h <;> omega

/-- The C5 fan-in-two component bound for a single-output weighted threshold circuit whose output
selects a gate. -/
theorem circuit_lt_of_inputSupport_card_le_two (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (h2 : ∀ j, (inputSupport c.program j).card ≤ 2) {L : ℕ} (hK : K ≤ 2 ^ L) :
    n < (inputGates c.program).card + 2 * L := by
  obtain ⟨gate, hgate⟩ := houtput
  apply lt_of_inputSupport_card_le_two c.program (fun z => z gate) ?_ hf h2 hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-! ### C6: Block-excess restriction and lower bound -/

/-- **Subset sum.** Items of weight at most `M` with total weight at least `2 * k + M` can be
partitioned into `𝒢 ⊆ 𝓑` and `𝓑 \ 𝒢` each of weight at least `k`. -/
theorem exists_subset_sum_ge {ι : Type*} [DecidableEq ι] (𝓑 : Finset ι) (φ : ι → ℕ)
    (M k : ℕ) (hφ : ∀ b ∈ 𝓑, φ b ≤ M) (htot : 2 * k + M ≤ ∑ b ∈ 𝓑, φ b) :
    ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ k ≤ ∑ b ∈ 𝓑 \ 𝒢, φ b := by
  have key : ∀ 𝓑 : Finset ι, (∀ b ∈ 𝓑, φ b ≤ M) → k ≤ ∑ b ∈ 𝓑, φ b →
      ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ ∑ b ∈ 𝒢, φ b ≤ k + M - 1 := by
    intro 𝓑
    induction 𝓑 using Finset.induction_on with
    | empty =>
      intro _ hk
      rw [sum_empty] at hk
      exact ⟨∅, Subset.refl _, by simpa using hk, by simp⟩
    | insert a t ha ih =>
      intro hφ hk
      rw [sum_insert ha] at hk
      by_cases hkt : k ≤ ∑ b ∈ t, φ b
      · obtain ⟨𝒢, h𝒢, h1, h2⟩ := ih (fun b hb => hφ b (mem_insert_of_mem hb)) hkt
        exact ⟨𝒢, h𝒢.trans (subset_insert _ _), h1, h2⟩
      · refine ⟨insert a t, Subset.refl _, ?_, ?_⟩
        · rw [sum_insert ha]
          exact hk
        · rw [sum_insert ha]
          have := hφ a (mem_insert_self _ _)
          omega
  obtain ⟨𝒢, h𝒢, h1, h2⟩ := key 𝓑 hφ (by omega)
  refine ⟨𝒢, h𝒢, h1, ?_⟩
  have := sum_sdiff (f := φ) h𝒢
  omega

private theorem sum_eq_sum_filter_add_sum_tsub_add_sum {ι : Type*} (𝓗 : Finset ι)
    (c e : ι → ℕ) :
    ∑ b ∈ 𝓗, c b = ∑ b ∈ 𝓗.filter (fun b => c b ≤ e b), c b + ∑ b ∈ 𝓗, (c b - e b) +
      ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), e b := by
  rw [← sum_filter_add_sum_filter_not 𝓗 (fun b => c b ≤ e b) c,
    ← sum_filter_add_sum_filter_not 𝓗 (fun b => c b ≤ e b) (fun b => c b - e b)]
  have h0 : ∑ b ∈ 𝓗.filter (fun b => c b ≤ e b), (c b - e b) = 0 :=
    sum_eq_zero fun b hb => Nat.sub_eq_zero_of_le (mem_filter.mp hb).2
  have h1 : ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), c b =
      ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), ((c b - e b) + e b) :=
    sum_congr rfl fun b hb =>
      (Nat.sub_add_cancel (le_of_lt (not_le.mp (mem_filter.mp hb).2))).symm
  rw [h0, h1, sum_add_distrib]
  omega

/-- The gates of `p` whose residual input support outside `F` is nonempty and contained in `b`. -/
noncomputable def residualGates (p : Program signature n g) (F b : Finset (Fin n)) :
    Finset (Fin g) :=
  univ.filter fun j => ¬ inputSupport p j ⊆ F ∧ inputSupport p j \ F ⊆ b

/-- A gate belongs to `residualGates p F b` if and only if its input support is not contained in
`F` and its residual support outside `F` is contained in `b`. -/
@[simp]
theorem mem_residualGates (p : Program signature n g) (F b : Finset (Fin n)) (j : Fin g) :
    j ∈ residualGates p F b ↔ ¬ inputSupport p j ⊆ F ∧ inputSupport p j \ F ⊆ b := by
  classical
  simp [residualGates]

/-- Every gate in `residualGates p F b` belongs to `inputGates p`. -/
theorem residualGates_subset_inputGates (p : Program signature n g) (F b : Finset (Fin n)) :
    residualGates p F b ⊆ inputGates p := by
  intro j hj
  rw [mem_residualGates] at hj
  rw [← inputSupport_ne_empty_iff]
  exact fun h0 => hj.1 (h0 ▸ empty_subset F)

private theorem disjoint_residualGates (p : Program signature n g) (F : Finset (Fin n))
    {b b' : Finset (Fin n)} (hbb' : Disjoint b b') :
    Disjoint (residualGates p F b) (residualGates p F b') := by
  rw [disjoint_left]
  intro j hj hj'
  rw [mem_residualGates] at hj hj'
  apply hj.1
  rw [← sdiff_eq_empty_iff_subset, eq_empty_iff_forall_notMem]
  intro i hi
  exact disjoint_left.mp hbb' (hj.2 hi) (hj'.2 hi)

/-- Over pairwise disjoint blocks `𝓑`, the total number of residual gates is at most
`(inputGates p).card`. -/
private theorem sum_card_residualGates_le (p : Program signature n g) (F : Finset (Fin n))
    (𝓑 : Finset (Finset (Fin n))) (hdisj : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id) :
    ∑ b ∈ 𝓑, (residualGates p F b).card ≤ (inputGates p).card := by
  classical
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.mpr fun b _ => residualGates_subset_inputGates p F b)
  · intro b hb b' hb' hne
    exact disjoint_residualGates p F (hdisj hb hb' hne)

private theorem card_filter_not_subset_le_sum_residualGates (p : Program signature n g)
    (F : Finset (Fin n)) (𝓑 𝓗 : Finset (Finset (Fin n)))
    (hblocks : ∀ j, inputSupport p j ⊆ F ∨ ∃ b ∈ 𝓑, inputSupport p j \ F ⊆ b)
    (W Y : Finset (Fin n))
    (hFY : ∀ i ∈ W, i ∈ F → i ∈ Y)
    (hW : ∀ b ∈ 𝓑, ∀ i ∈ b, i ∈ W → b ∈ 𝓗)
    (hY : ∀ b ∈ 𝓗, b.card ≤ (residualGates p F b).card → b ⊆ Y) :
    (univ.filter fun j => ¬ inputSupport p j ∩ W ⊆ Y).card ≤
      ∑ b ∈ 𝓗.filter (fun b => ¬ b.card ≤ (residualGates p F b).card),
        (residualGates p F b).card := by
  classical
  refine le_trans (card_le_card (t := (𝓗.filter
    fun b => ¬ b.card ≤ (residualGates p F b).card).biUnion (residualGates p F)) ?_)
    card_biUnion_le
  intro j hj
  rw [mem_filter] at hj
  obtain ⟨i, hiW_inter, hiY⟩ := not_subset.mp hj.2
  obtain ⟨hi_supp, hiW⟩ := mem_inter.mp hiW_inter
  have hiF : i ∉ F := fun hiF => hiY (hFY i hiW hiF)
  have hisdiff : i ∈ inputSupport p j \ F := mem_sdiff.mpr ⟨hi_supp, hiF⟩
  have hne : ¬ inputSupport p j ⊆ F := fun h => hiF (h hi_supp)
  obtain ⟨b, hb, hsub⟩ := (hblocks j).resolve_left hne
  have hbH : b ∈ 𝓗 := hW b hb i (hsub hisdiff) hiW
  rw [mem_biUnion]
  refine ⟨b, mem_filter.mpr ⟨hbH, fun hsat => hiY (hY b hbH hsat (hsub hisdiff))⟩, ?_⟩
  exact (mem_residualGates p F b j).mpr ⟨hne, hsub⟩

/-- **C6: the block-excess lower bound.** Let `F` be a set of inputs and `𝓑` a family of
pairwise disjoint blocks covering the inputs outside `F`, such that every gate reads inputs from
`F` only or has its residual support outside `F` inside a single block of `𝓑`. If every block `b`
has excess `|b| - e_b ≤ M`, where `e_b = (residualGates p F b).card`, and `p` computes a
two-sided `K`-rectangle-free function `f` through `readout` with `K ≤ 2 ^ k`, then
`n < F.card + (inputGates p).card + M + 2 * k`. -/
theorem lt_of_blocks (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (F : Finset (Fin n)) (𝓑 : Finset (Finset (Fin n)))
    (hdisj : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : ∀ i, i ∉ F → ∃ b ∈ 𝓑, i ∈ b)
    (hF : ∀ b ∈ 𝓑, Disjoint b F)
    (hblocks : ∀ j, inputSupport p j ⊆ F ∨ ∃ b ∈ 𝓑, inputSupport p j \ F ⊆ b)
    (M : ℕ) (hM : ∀ b ∈ 𝓑, b.card ≤ (residualGates p F b).card + M)
    {k : ℕ} (hK : K ≤ 2 ^ k) :
    n < F.card + (inputGates p).card + M + 2 * k := by
  classical
  by_contra hn
  push Not at hn
  have hbU : 𝓑.biUnion id = Fᶜ := by
    ext i
    simp only [mem_biUnion, id, mem_compl]
    constructor
    · rintro ⟨b, hb, hi⟩
      exact disjoint_left.mp (hF b hb) hi
    · exact hcover i
  have hFn : F.card ≤ n := by simpa using card_le_univ F
  have hsumcard : ∑ b ∈ 𝓑, b.card = n - F.card := by
    calc ∑ b ∈ 𝓑, b.card = (𝓑.biUnion id).card := (card_biUnion hdisj).symm
      _ = n - F.card := by rw [hbU, card_compl, Fintype.card_fin]
  have hsume := sum_card_residualGates_le p F 𝓑 hdisj
  have hφtot : 2 * k + M ≤ ∑ b ∈ 𝓑, (b.card - (residualGates p F b).card) := by
    have h1 : ∑ b ∈ 𝓑, b.card ≤
        ∑ b ∈ 𝓑, ((b.card - (residualGates p F b).card) + (residualGates p F b).card) :=
      sum_le_sum fun b _ => le_tsub_add
    rw [sum_add_distrib] at h1
    omega
  obtain ⟨𝒢, h𝒢, hk1, hk2⟩ := exists_subset_sum_ge 𝓑
    (fun b => b.card - (residualGates p F b).card) M k
    (fun b hb => by
      have := hM b hb
      omega) hφtot
  set U := 𝒢.biUnion id with hU
  set A := (𝒢.filter fun b => b.card ≤ (residualGates p F b).card).biUnion id with hA
  set B₀ := ((𝓑 \ 𝒢).filter fun b => b.card ≤ (residualGates p F b).card).biUnion id with hB₀
  have hdisjU : ∀ b ∈ 𝓑, b ∉ 𝒢 → Disjoint b U := by
    intro b hb hbG
    rw [hU, disjoint_biUnion_right]
    intro b' hb'
    exact hdisj hb (h𝒢 hb') fun h => hbG (h ▸ hb')
  have hFU : Disjoint F U := by
    rw [hU, disjoint_biUnion_right]
    intro b' hb'
    exact (hF b' (h𝒢 hb')).symm
  have hAU : A ⊆ U :=
    biUnion_subset_biUnion_of_subset_left _ (filter_subset _ _)
  have hB₀U : B₀ ⊆ Uᶜ := by
    rw [hB₀, subset_compl_iff_disjoint_right, disjoint_biUnion_left]
    intro b hb
    have hb' := mem_sdiff.mp (mem_filter.mp hb).1
    exact hdisjU b hb'.1 hb'.2
  have hFUc : F ⊆ Uᶜ := subset_compl_iff_disjoint_right.mpr hFU
  have hFB₀U : F ∪ B₀ ⊆ Uᶜ := union_subset hFUc hB₀U
  have hdisjFB₀ : Disjoint F B₀ := by
    rw [hB₀, disjoint_biUnion_right]
    intro b hb
    exact (hF b (sdiff_subset (mem_filter.mp hb).1)).symm
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := exists_rectangle_of_cut_with_fixed p U A (F ∪ B₀) hAU hFB₀U
  have hconst : ∀ x ∈ P, ∀ y ∈ Q, f (glue U x y) = readout v := by
    intro x hx y hy
    rw [← hreadout, hv x hx y hy]
  -- Bound on the `P` side.
  have hUcard : U.card = ∑ b ∈ 𝒢, b.card :=
    card_biUnion (hdisj.subset (coe_subset.mpr h𝒢))
  have hAcard : A.card = ∑ b ∈ 𝒢.filter (fun b => b.card ≤ (residualGates p F b).card), b.card :=
    card_biUnion (hdisj.subset (coe_subset.mpr ((filter_subset _ _).trans h𝒢)))
  have hgP := card_filter_not_subset_le_sum_residualGates p F 𝓑 𝒢 hblocks U A
    (fun i hiU hiF => (disjoint_left.mp hFU hiF hiU).elim)
    (fun b hb i hi hiU => by
      by_contra hbG
      exact disjoint_left.mp (hdisjU b hb hbG) hi hiU)
    (fun b hb hsat => subset_biUnion_of_mem id (mem_filter.mpr ⟨hb, hsat⟩))
  have hdecompP := sum_eq_sum_filter_add_sum_tsub_add_sum 𝒢 Finset.card
    fun b => (residualGates p F b).card
  have hPK : K ≤ P.card := le_card_of_pow_le hP (by omega) hK
  -- Bound on the `Q` side.
  have hUc : Uᶜ.card = n - U.card := by rw [card_compl, Fintype.card_fin]
  have hsplitsum : ∑ b ∈ 𝓑 \ 𝒢, b.card + ∑ b ∈ 𝒢, b.card = ∑ b ∈ 𝓑, b.card :=
    sum_sdiff h𝒢
  have hB₀card : B₀.card =
      ∑ b ∈ (𝓑 \ 𝒢).filter (fun b => b.card ≤ (residualGates p F b).card), b.card :=
    card_biUnion (hdisj.subset
      (coe_subset.mpr ((filter_subset _ _).trans sdiff_subset)))
  have hFB₀card : (F ∪ B₀).card = F.card + B₀.card := card_union_of_disjoint hdisjFB₀
  have hgQ := card_filter_not_subset_le_sum_residualGates p F 𝓑 (𝓑 \ 𝒢) hblocks Uᶜ (F ∪ B₀)
    (fun _ _ hiF => mem_union_left B₀ hiF)
    (fun b hb i hi hiU => mem_sdiff.mpr ⟨hb, fun hbG =>
      mem_compl.mp hiU (subset_biUnion_of_mem id hbG hi)⟩)
    (fun b hb hsat =>
      (subset_biUnion_of_mem id (mem_filter.mpr ⟨hb, hsat⟩)).trans (subset_union_right))
  have hdecompQ := sum_eq_sum_filter_add_sum_tsub_add_sum (𝓑 \ 𝒢) Finset.card
    fun b => (residualGates p F b).card
  have hQK : K ≤ Q.card := le_card_of_pow_le hQ (by omega) hK
  rcases card_lt_or_card_lt_of_rectangleFree hf U P Q (readout v) hconst with h | h <;> omega

/-- The C6 block-excess bound for a single-output weighted threshold circuit whose output selects a
gate. -/
theorem circuit_lt_of_blocks (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (F : Finset (Fin n)) (𝓑 : Finset (Finset (Fin n)))
    (hdisj : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : ∀ i, i ∉ F → ∃ b ∈ 𝓑, i ∈ b)
    (hF : ∀ b ∈ 𝓑, Disjoint b F)
    (hblocks : ∀ j, inputSupport c.program j ⊆ F ∨ ∃ b ∈ 𝓑, inputSupport c.program j \ F ⊆ b)
    (M : ℕ) (hM : ∀ b ∈ 𝓑, b.card ≤ (residualGates c.program F b).card + M)
    {k : ℕ} (hK : K ≤ 2 ^ k) :
    n < F.card + (inputGates c.program).card + M + 2 * k := by
  obtain ⟨gate, hgate⟩ := houtput
  apply lt_of_blocks c.program (fun z => z gate) ?_ hf F 𝓑 hdisj hcover hF hblocks M hM hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

end Cslib.Circuits.Boolean.WeightedThreshold
