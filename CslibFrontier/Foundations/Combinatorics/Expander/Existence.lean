/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Family
public import CslibFrontier.Foundations.Combinatorics.Expander.Lazy
public import CslibFrontier.Foundations.Combinatorics.Expander.Perm
import CslibFrontier.Foundations.Combinatorics.Expander.Random

/-!
# Constant-degree expanders exist

Every finite type `V` carries a `120`-regular multigraph of spectral expansion at most
`1 - 1 / 360000` (`exists_spectralExpansion_le`): constant-degree expanders exist on any number of
vertices, with a degree and a spectral bound that do not depend on that number
(`exists_forall_exists_spectralExpansion_le`). The proof combines three ingredients.

* Thirty permutations of `V` move a tenth of every set of at most half of the vertices out of it
  (`Cslib.exists_perms_card_le_mul_card_filter_notMem`, a counting argument).
* Their `60`-regular multigraph `Cslib.RotationMap.ofPerms` therefore has edge expansion at least
  `1 / 5` (`Cslib.RotationMap.le_edgeExpansion_ofPerms`).
* Cheeger's inequality turns edge expansion into a spectral bound for its lazy graph, of degree
  `120` (`Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`).

The construction is not explicit, since the permutations come from a counting argument, and neither
is the multigraph `expander V` chosen from it. Explicit families are built by graph products from a
single expander of constant size
[Reingold, Vadhan and Wigderson, Section 1.2][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09].

The multigraphs `expander V` form a family of expanders (`Cslib.RotationMap.ExpanderFamily`,
`expanderFamily`), as Dinur's preprocessing needs [Dinur, Section 3.1][Dinur2005].

## Main definitions

* `Cslib.RotationMap.expander`: a `120`-regular multigraph on `V` of spectral expansion at most
  `1 - 1 / 360000`, chosen non-constructively.
* `Cslib.RotationMap.expanderFamily`: the family of the multigraphs `expander V`.

## Main results

* `Cslib.RotationMap.exists_spectralExpansion_le`: such a multigraph exists on every finite type.
* `Cslib.RotationMap.exists_forall_exists_spectralExpansion_le`: constant-degree expanders exist,
  with the same degree and spectral bound on every finite type.
* `Cslib.RotationMap.le_edgeExpansion_expander`: they have edge expansion at least `1 / 6000`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

universe u

variable (V : Type u) [Fintype V]

/-- **Constant-degree expanders exist**
[Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09]: every finite type carries a `120`-regular multigraph of
spectral expansion at most `1 - 1 / 360000`. It is the lazy graph of the multigraph of thirty
permutations that move a tenth of every set of at most half of the vertices out of it. -/
theorem exists_spectralExpansion_le :
    ∃ G : RotationMap V (Fin 120), G.spectralExpansion ≤ 1 - 1 / 360000 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perms_card_le_mul_card_filter_notMem V
  have hcard : Fintype.card ((Fin 30 × Bool) ⊕ (Fin 30 × Bool)) = 120 := by simp
  refine ⟨(ofPerms σ).lazy.relabel (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [spectralExpansion_relabel]
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [spectralExpansion_eq_zero_of_subsingleton]
    norm_num
  refine ((ofPerms σ).spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl
    (c := 1 / 5) (by norm_num) fun S hS ↦ ?_).trans (le_of_eq ?_)
  · obtain ⟨i, hi⟩ := hσ S hS
    have hle : #{v ∈ S | σ i v ∉ S} ≤ ∑ j, #{v ∈ S | σ j v ∉ S} :=
      single_le_sum (f := fun j ↦ #{v ∈ S | σ j v ∉ S}) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    have : (#S : ℝ) ≤ 10 * ∑ j, #{v ∈ S | σ j v ∉ S} := by exact_mod_cast hi.trans (by omega)
    rw [card_interedges_compl_ofPerms]
    push_cast at this ⊢
    linarith
  · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    norm_num

/-- **Constant-degree expanders exist**
[Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09]: there are a degree `d` and a bound `μ < 1` such that
every finite type carries a `d`-regular multigraph of spectral expansion at most `μ`. -/
theorem exists_forall_exists_spectralExpansion_le :
    ∃ d : ℕ, ∃ μ < 1, ∀ (V : Type u) [Fintype V],
      ∃ G : RotationMap V (Fin d), G.spectralExpansion ≤ μ :=
  ⟨120, 1 - 1 / 360000, by norm_num, fun V _ ↦ exists_spectralExpansion_le V⟩

/-- A `120`-regular multigraph on a finite type `V` of spectral expansion at most
`1 - 1 / 360000` (`spectralExpansion_expander_le`), chosen non-constructively by
`exists_spectralExpansion_le`. -/
noncomputable def expander : RotationMap V (Fin 120) :=
  (exists_spectralExpansion_le V).choose

/-- The spectral expansion of `expander V` is at most `1 - 1 / 360000`. -/
theorem spectralExpansion_expander_le : (expander V).spectralExpansion ≤ 1 - 1 / 360000 :=
  (exists_spectralExpansion_le V).choose_spec

/-- The non-explicit family of the `120`-regular multigraphs `expander V`, of spectral expansion
at most `1 - 1 / 360000`. -/
noncomputable def expanderFamily : ExpanderFamily.{u} (Fin 120) (1 - 1 / 360000) where
  graph V _ := expander V
  spectralExpansion_graph_le V _ := spectralExpansion_expander_le V

/-- The multigraph of `expanderFamily` on `V` is `expander V`. -/
@[simp]
theorem graph_expanderFamily (V : Type u) [Fintype V] : expanderFamily.graph V = expander V :=
  rfl

/-- On at least two vertices, `expander V` has edge expansion at least `1 / 6000`. -/
theorem le_edgeExpansion_expander [DecidableEq V] [Nontrivial V] :
    1 / 6000 ≤ (expander V).edgeExpansion := by
  have h := le_edgeExpansion_of_spectralExpansion_le (spectralExpansion_expander_le V)
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

end Cslib.RotationMap
