/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Nice.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Subtree
public import Mathlib.Data.Finset.Sort

/-!
# Nice tree decompositions

A *nice tree decomposition* (`SimpleGraph.NiceTreeDecomposition G`) is a rooted binary tree
decomposition whose root and leaves have empty bags and whose every internal node is of three types
([CyganEtAl2015]):

* **Leaf**: no children, empty bag `∅`.
* **Introduce `v`**: one child `child` with `v` outside `child.subtreeVerts` and
  `bag = insert v child.bag`.
* **Forget `v`**: one child `child` with `v ∈ child.bag` and `bag = child.bag.erase v`.
* **Join**: two children `left`, `right` with `left.bag = right.bag = bag` and
  `Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts`.

We model the syntax algebraically as `SimpleGraph.NiceTree V`, define its validity
(`NiceTree.LocalValid`, `NiceTree.CoversFinset`) and conversion to
`SimpleGraph.RootedTreeDecomposition` (`NiceTree.toRootedTreeDecomposition`), and prove that every
finite clique lies in some bag (`NiceTree.exists_coversFinset_of_isClique`). Conversely,
`RootedTreeDecomposition.prune` contracts redundant subset bags so that a finite vertex type
leaves at most `card V + 1` nodes without increasing width, and `RootedTreeDecomposition.toNiceTree`
(computable when `[LinearOrder V]`, with noncomputable `[DecidableEq V]` counterpart
`RootedTreeDecomposition.toNice`) converts any finite rooted or unrooted tree decomposition into a
`NiceTreeDecomposition G` with width at most the original width and at most
`(3 * width + 5) * (card V + 1)` nodes.

## Main definitions

* `SimpleGraph.NiceTree`: algebraic syntax of leaf/introduce/forget/join tree decompositions.
* `SimpleGraph.NiceTreeDecomposition`: bundled nice tree decomposition of `G` with empty root bag.
* `SimpleGraph.NiceTree.toRootedTreeDecomposition`: parent-array rooted decomposition of a valid
  `NiceTree`.
* `SimpleGraph.RootedTreeDecomposition.prune`: contraction eliminating redundant subset children,
  leaving at most `Fintype.card V + 1` nodes.
* `SimpleGraph.RootedTreeDecomposition.toNiceTree`, `SimpleGraph.RootedTreeDecomposition.toNice`,
  `SimpleGraph.TreeDecomposition.exists_niceTreeDecomposition`: conversion to a nice tree
  decomposition without increasing width.

## Main results

* `SimpleGraph.NiceTree.exists_coversFinset_of_isClique`: every finite clique lies in some bag.
* `SimpleGraph.RootedTreeDecomposition.prune_width_le`,
  `SimpleGraph.RootedTreeDecomposition.prune_nodes_le`: width and `O(|V|)` node bounds for pruning.
* `SimpleGraph.RootedTreeDecomposition.toNiceTree_width_le`,
  `SimpleGraph.RootedTreeDecomposition.toNiceTree_size_le`: width does not increase and node count
  is at most `(3 * R.width + 5) * (n + 1)` (hence `≤ (3 * R.width + 5) * (card V + 1)` after
  pruning).

## References

* [M. Cygan et al., *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace SimpleGraph

universe uV uι

/-! ### Nice tree decomposition syntax and invariants -/

/-- Algebraic tree structure for a nice tree decomposition over vertex type `V`. -/
inductive NiceTree (V : Type uV)
  | leaf : NiceTree V
  | introduce (v : V) (child : NiceTree V) : NiceTree V
  | forget (v : V) (child : NiceTree V) : NiceTree V
  | join (left right : NiceTree V) : NiceTree V
  deriving DecidableEq, Repr

namespace NiceTree

variable {V : Type uV} {G : SimpleGraph V}

/-- Total number of nodes minus one in a `NiceTree`. -/
@[expose] def sizePred : NiceTree V → ℕ
  | .leaf => 0
  | .introduce _ child => child.sizePred + 1
  | .forget _ child => child.sizePred + 1
  | .join left right => left.sizePred + right.sizePred + 2

/-- Total number of nodes in a `NiceTree`. -/
@[expose] def size (T : NiceTree V) : ℕ :=
  T.sizePred + 1

@[simp] theorem size_leaf : (.leaf : NiceTree V).size = 1 := rfl
@[simp] theorem size_introduce (v : V) (child : NiceTree V) :
    (NiceTree.introduce v child).size = child.size + 1 := rfl
@[simp] theorem size_forget (v : V) (child : NiceTree V) :
    (NiceTree.forget v child).size = child.size + 1 := rfl
@[simp] theorem size_join (left right : NiceTree V) :
    (NiceTree.join left right).size = left.size + right.size + 1 := by
  simp only [size, sizePred]; omega

theorem size_pos (T : NiceTree V) : 0 < T.size := by
  unfold size; omega

section Decidable

variable [DecidableEq V]

/-- The bag of vertices associated with the root node of `T`. -/
@[expose] def bag : NiceTree V → Finset V
  | .leaf => ∅
  | .introduce v child => insert v child.bag
  | .forget v child => child.bag.erase v
  | .join left _ => left.bag

/-- Maximum bag cardinality over all nodes in `T`. -/
@[expose] def maxBagCard : NiceTree V → ℕ
  | .leaf => 0
  | .introduce v child => max (insert v child.bag).card child.maxBagCard
  | .forget v child => max (child.bag.erase v).card child.maxBagCard
  | .join left right => max left.bag.card (max left.maxBagCard right.maxBagCard)

/-- Width of a `NiceTree`: largest bag size minus one. -/
@[expose] def width (T : NiceTree V) : ℕ :=
  T.maxBagCard - 1

theorem card_bag_le_maxBagCard (T : NiceTree V) : T.bag.card ≤ T.maxBagCard := by
  cases T <;> simp [bag, maxBagCard]

theorem width_le_iff {T : NiceTree V} {k : ℕ} : T.width ≤ k ↔ T.maxBagCard ≤ k + 1 := by
  unfold width
  omega

/-- Union of all bags occurring in the subtree `T`. -/
@[expose] def subtreeVerts : NiceTree V → Finset V
  | .leaf => ∅
  | .introduce v child => insert v child.subtreeVerts
  | .forget _ child => child.subtreeVerts
  | .join left right => left.subtreeVerts ∪ right.subtreeVerts

theorem bag_subset_subtreeVerts (T : NiceTree V) : T.bag ⊆ T.subtreeVerts := by
  induction T with
  | leaf => exact Finset.Subset.rfl
  | introduce v child ih => exact Finset.insert_subset_insert v ih
  | forget v child ih => exact (Finset.erase_subset v _).trans ih
  | join left _ ihL _ => exact ihL.trans Finset.subset_union_left

/-- Local nice-tree invariant at every node: `introduce` introduces a vertex not appearing anywhere
in the child's subtree, `forget` removes a vertex present in the child bag, and `join` combines two
children with identical bags whose forgotten subtrees are disjoint. -/
@[expose] def LocalValid : NiceTree V → Prop
  | .leaf => True
  | .introduce v child => v ∉ child.subtreeVerts ∧ child.LocalValid
  | .forget v child => v ∈ child.bag ∧ child.LocalValid
  | .join left right =>
    left.bag = right.bag ∧
      Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts ∧
      left.LocalValid ∧ right.LocalValid

instance decidableLocalValid : (T : NiceTree V) → Decidable T.LocalValid
  | .leaf => isTrue trivial
  | .introduce _ child =>
    letI := decidableLocalValid child
    instDecidableAnd
  | .forget _ child =>
    letI := decidableLocalValid child
    instDecidableAnd
  | .join left right =>
    letI := decidableLocalValid left
    letI := decidableLocalValid right
    instDecidableAnd

/-- Symmetry of the join subtree-separation condition. -/
theorem disjoint_join_right {left right : NiceTree V} (hbag : left.bag = right.bag)
    (hdisj : Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts) :
    Disjoint (right.subtreeVerts \ right.bag) left.subtreeVerts := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hxR hxL
  rw [Finset.mem_sdiff, ← hbag] at hxR
  exact hdisj (Finset.mem_sdiff.2 ⟨hxL, hxR.2⟩) hxR.1

/-- `K` is contained in at least one node's bag in `T`. -/
@[expose] def CoversFinset (K : Finset V) : NiceTree V → Prop
  | .leaf => K ⊆ ∅
  | .introduce v child => K ⊆ insert v child.bag ∨ child.CoversFinset K
  | .forget v child => K ⊆ child.bag.erase v ∨ child.CoversFinset K
  | .join left right => K ⊆ left.bag ∨ left.CoversFinset K ∨ right.CoversFinset K

theorem coversFinset_of_subset_bag {T : NiceTree V} {K : Finset V} (h : K ⊆ T.bag) :
    T.CoversFinset K := by
  cases T with
  | leaf => exact h
  | introduce _ _ => exact Or.inl h
  | forget _ _ => exact Or.inl h
  | join _ _ => exact Or.inl h

theorem coversFinset_mono {T : NiceTree V} {K₁ K₂ : Finset V} (hsub : K₁ ⊆ K₂)
    (h : T.CoversFinset K₂) : T.CoversFinset K₁ := by
  induction T with
  | leaf => exact hsub.trans h
  | introduce v child ih =>
    rcases h with h | h
    · exact Or.inl (hsub.trans h)
    · exact Or.inr (ih h)
  | forget v child ih =>
    rcases h with h | h
    · exact Or.inl (hsub.trans h)
    · exact Or.inr (ih h)
  | join left right ihL ihR =>
    rcases h with h | h | h
    · exact Or.inl (hsub.trans h)
    · exact Or.inr (Or.inl (ihL h))
    · exact Or.inr (Or.inr (ihR h))

theorem coversFinset_subset_subtreeVerts {T : NiceTree V} {K : Finset V}
    (h : T.CoversFinset K) : K ⊆ T.subtreeVerts := by
  induction T with
  | leaf => exact h
  | introduce v child ih =>
    rcases h with h | h
    · exact h.trans (Finset.insert_subset_insert v child.bag_subset_subtreeVerts)
    · exact (ih h).trans (Finset.subset_insert v _)
  | forget v child ih =>
    rcases h with h | h
    · exact h.trans ((Finset.erase_subset v _).trans child.bag_subset_subtreeVerts)
    · exact ih h
  | join left right ihL ihR =>
    rcases h with h | h | h
    · exact h.trans (left.bag_subset_subtreeVerts.trans Finset.subset_union_left)
    · exact (ihL h).trans Finset.subset_union_left
    · exact (ihR h).trans Finset.subset_union_right

theorem coversFinset_singleton_of_mem_subtreeVerts {T : NiceTree V} {v : V}
    (hv : v ∈ T.subtreeVerts) : T.CoversFinset {v} := by
  induction T with
  | leaf => simp [subtreeVerts] at hv
  | introduce w child ih =>
    rcases Finset.mem_insert.1 hv with rfl | hvc
    · exact coversFinset_of_subset_bag (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
    · exact Or.inr (ih hvc)
  | forget w child ih => exact Or.inr (ih hv)
  | join left right ihL ihR =>
    rcases Finset.mem_union.1 hv with hvL | hvR
    · exact Or.inr (Or.inl (ihL hvL))
    · exact Or.inr (Or.inr (ihR hvR))

/-- Every finite clique contained in `T.subtreeVerts` lies in some bag of `T` whenever every
edge of `G` inside `T.subtreeVerts` is covered. -/
theorem exists_coversFinset_of_isClique {T : NiceTree V} (hvalid : T.LocalValid)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ T.subtreeVerts → v ∈ T.subtreeVerts →
      T.CoversFinset {u, v})
    {K : Finset V} (hK : G.IsClique (K : Set V)) (hsub : K ⊆ T.subtreeVerts) :
    T.CoversFinset K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact coversFinset_of_subset_bag (Finset.empty_subset _)
  induction T with
  | leaf =>
    obtain ⟨v, hv⟩ := hne
    exact absurd (hsub hv) (Finset.notMem_empty v)
  | introduce v child ih =>
    obtain ⟨hv_sub, hc⟩ := hvalid
    by_cases hvK : v ∈ K
    · refine Or.inl fun w hw => ?_
      by_cases hwv : w = v
      · subst hwv; exact Finset.mem_insert_self _ _
      · have hadj : G.Adj v w := hK hvK hw (Ne.symm hwv)
        rcases hedge hadj (Finset.mem_insert_self _ _) (hsub hw) with hpair | hcov
        · exact hpair (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        · exact absurd (coversFinset_subset_subtreeVerts hcov (Finset.mem_insert_self v _)) hv_sub
    · have hsub' : K ⊆ child.subtreeVerts := fun w hw => by
        rcases Finset.mem_insert.1 (hsub hw) with rfl | hwc
        · exact absurd hw hvK
        · exact hwc
      have hedge' : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ child.subtreeVerts → y ∈ child.subtreeVerts →
          child.CoversFinset {x, y} := by
        intro x y hxy hx hy
        rcases hedge hxy (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) with
          hp | hc_cov
        · have hxne : x ≠ v := fun h => hv_sub (h ▸ hx)
          have hyne : y ≠ v := fun h => hv_sub (h ▸ hy)
          refine coversFinset_of_subset_bag fun z hz => ?_
          rcases Finset.mem_insert.1 (hp hz) with rfl | hz''
          · rcases Finset.mem_insert.1 hz with rfl | hzv
            · exact absurd rfl hxne
            · rw [Finset.mem_singleton] at hzv
              exact absurd hzv hyne.symm
          · exact hz''
        · exact hc_cov
      exact Or.inr (ih hc hedge' hsub')
  | forget v child ih =>
    obtain ⟨_, hc⟩ := hvalid
    have hedge' : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ child.subtreeVerts → y ∈ child.subtreeVerts →
        child.CoversFinset {x, y} := by
      intro x y hxy hx hy
      rcases hedge hxy hx hy with hp | hc_cov
      · exact coversFinset_of_subset_bag (hp.trans (Finset.erase_subset v _))
      · exact hc_cov
    exact Or.inr (ih hc hedge' hsub)
  | join left right ihL ihR =>
    obtain ⟨hbag, hdisj, hcL, hcR⟩ := hvalid
    have hedgeL : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ left.subtreeVerts → y ∈ left.subtreeVerts →
        left.CoversFinset {x, y} := by
      intro x y hxy hx hy
      rcases hedge hxy (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy) with
        hp | hL | hR
      · exact coversFinset_of_subset_bag hp
      · exact hL
      · have hxR := coversFinset_subset_subtreeVerts hR (Finset.mem_insert_self x _)
        have hyR := coversFinset_subset_subtreeVerts hR
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        have hxB : x ∈ left.bag := by
          by_contra hxB
          exact Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.2 ⟨hx, hxB⟩) hxR
        have hyB : y ∈ left.bag := by
          by_contra hyB
          exact Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.2 ⟨hy, hyB⟩) hyR
        exact coversFinset_of_subset_bag
          (Finset.insert_subset hxB (Finset.singleton_subset_iff.2 hyB))
    have hdisjR := disjoint_join_right hbag hdisj
    have hedgeR : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ right.subtreeVerts → y ∈ right.subtreeVerts →
        right.CoversFinset {x, y} := by
      intro x y hxy hx hy
      rcases hedge hxy (Finset.mem_union_right _ hx) (Finset.mem_union_right _ hy) with
        hp | hL | hR
      · exact coversFinset_of_subset_bag (hbag ▸ hp)
      · have hxL := coversFinset_subset_subtreeVerts hL (Finset.mem_insert_self x _)
        have hyL := coversFinset_subset_subtreeVerts hL
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        have hxB : x ∈ right.bag := by
          by_contra hxB
          exact Finset.disjoint_left.1 hdisjR (Finset.mem_sdiff.2 ⟨hx, hxB⟩) hxL
        have hyB : y ∈ right.bag := by
          by_contra hyB
          exact Finset.disjoint_left.1 hdisjR (Finset.mem_sdiff.2 ⟨hy, hyB⟩) hyL
        exact coversFinset_of_subset_bag
          (Finset.insert_subset hxB (Finset.singleton_subset_iff.2 hyB))
      · exact hR
    by_cases hL : K ⊆ left.subtreeVerts
    · exact Or.inr (Or.inl (ihL hcL hedgeL hL))
    · by_cases hR : K ⊆ right.subtreeVerts
      · exact Or.inr (Or.inr (ihR hcR hedgeR hR))
      · obtain ⟨u, huK, huL⟩ := Finset.not_subset.1 hL
        obtain ⟨w, hwK, hwR⟩ := Finset.not_subset.1 hR
        have huR : u ∈ right.subtreeVerts := (Finset.mem_union.1 (hsub huK)).resolve_left huL
        have hwL : w ∈ left.subtreeVerts := (Finset.mem_union.1 (hsub hwK)).resolve_right hwR
        have huw : u ≠ w := fun h => huL (h ▸ hwL)
        rcases hedge (hK huK hwK huw) (hsub huK) (hsub hwK) with hp | hcovL | hcovR
        · exact absurd (left.bag_subset_subtreeVerts (hp (Finset.mem_insert_self u _))) huL
        · exact absurd (coversFinset_subset_subtreeVerts hcovL (Finset.mem_insert_self u _)) huL
        · exact absurd (coversFinset_subset_subtreeVerts hcovR
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))) hwR

end Decidable

section Map

variable {α : Type*} {β : Type*}

/-- Relabel the vertices of a `NiceTree` along `f`. -/
@[expose] def map (f : α → β) : NiceTree α → NiceTree β
  | .leaf => .leaf
  | .introduce v child => .introduce (f v) (map f child)
  | .forget v child => .forget (f v) (map f child)
  | .join left right => .join (map f left) (map f right)

@[simp] theorem sizePred_map (f : α → β) (T : NiceTree α) : (T.map f).sizePred = T.sizePred := by
  induction T with
  | leaf => rfl
  | introduce _ _ ih => simp [map, sizePred, ih]
  | forget _ _ ih => simp [map, sizePred, ih]
  | join _ _ ihL ihR => simp [map, sizePred, ihL, ihR]

@[simp] theorem size_map (f : α → β) (T : NiceTree α) : (T.map f).size = T.size := by
  simp [size]

theorem bag_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).bag = T.bag.image f := by
  induction T with
  | leaf => simp [map, bag]
  | introduce v child ih => simp [map, bag, ih, Finset.image_insert]
  | forget v child ih => simp [map, bag, ih, Finset.image_erase hf]
  | join left _ ihL _ => simp [map, bag, ihL]

theorem subtreeVerts_map (f : α → β) (T : NiceTree α) [DecidableEq α] [DecidableEq β] :
    (T.map f).subtreeVerts = T.subtreeVerts.image f := by
  induction T with
  | leaf => simp [map, subtreeVerts]
  | introduce v child ih => simp [map, subtreeVerts, ih, Finset.image_insert]
  | forget _ child ih => simp [map, subtreeVerts, ih]
  | join left right ihL ihR => simp [map, subtreeVerts, ihL, ihR, Finset.image_union]

theorem localValid_map {f : α → β} (hf : Function.Injective f) {T : NiceTree α}
    [DecidableEq α] [DecidableEq β] (h : T.LocalValid) : (T.map f).LocalValid := by
  induction T with
  | leaf => trivial
  | introduce v child ih =>
    refine ⟨?_, ih h.2⟩
    rw [subtreeVerts_map, Finset.mem_image]
    rintro ⟨u, hu, hu_eq⟩
    exact h.1 (hf hu_eq ▸ hu)
  | forget v child ih =>
    refine ⟨?_, ih h.2⟩
    rw [bag_map hf]
    exact Finset.mem_image_of_mem f h.1
  | join left right ihL ihR =>
    refine ⟨?_, ?_, ihL h.2.2.1, ihR h.2.2.2⟩
    · rw [bag_map hf, bag_map hf, h.1]
    · rw [subtreeVerts_map, bag_map hf, subtreeVerts_map, Finset.disjoint_left]
      intro y hyL hyR
      rw [Finset.mem_sdiff, Finset.mem_image, Finset.mem_image] at hyL
      obtain ⟨⟨x, hxL, rfl⟩, hxB⟩ := hyL
      obtain ⟨z, hzR, hxz⟩ := Finset.mem_image.1 hyR
      have hne : x ∉ left.bag := fun hx => hxB ⟨x, hx, rfl⟩
      exact Finset.disjoint_left.1 h.2.1 (Finset.mem_sdiff.2 ⟨hxL, hne⟩) (hf hxz ▸ hzR)

theorem maxBagCard_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).maxBagCard = T.maxBagCard := by
  induction T with
  | leaf => rfl
  | introduce v child ih =>
    simp only [map, maxBagCard]
    rw [bag_map hf, ← Finset.image_insert, Finset.card_image_of_injective _ hf, ih]
  | forget v child ih =>
    simp only [map, maxBagCard]
    rw [bag_map hf, ← Finset.image_erase hf, Finset.card_image_of_injective _ hf, ih]
  | join left right ihL ihR =>
    simp only [map, maxBagCard, bag_map hf, Finset.card_image_of_injective _ hf, ihL, ihR]

theorem width_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).width = T.width := by
  simp [width, maxBagCard_map hf]

theorem coversFinset_map {f : α → β} (hf : Function.Injective f) {T : NiceTree α}
    {K : Finset α} [DecidableEq α] [DecidableEq β] (h : T.CoversFinset K) :
    (T.map f).CoversFinset (K.image f) := by
  induction T with
  | leaf => simpa [map, CoversFinset] using h
  | introduce v child ih =>
    rcases h with h | h
    · left
      rw [bag_map hf, ← Finset.image_insert]
      exact Finset.image_subset_image h
    · exact Or.inr (ih h)
  | forget v child ih =>
    rcases h with h | h
    · left
      rw [bag_map hf, ← Finset.image_erase hf]
      exact Finset.image_subset_image h
    · exact Or.inr (ih h)
  | join left right ihL ihR =>
    rcases h with h | h | h
    · left
      rw [bag_map hf]
      exact Finset.image_subset_image h
    · exact Or.inr (Or.inl (ihL h))
    · exact Or.inr (Or.inr (ihR h))

end Map

end NiceTree

/-! ### Bundled nice tree decomposition -/

section Bundled

variable {V : Type uV}

/-- A nice tree decomposition of `G`: a valid `NiceTree V` with empty root bag that covers all
vertices and edges of `G`. -/
structure NiceTreeDecomposition (G : SimpleGraph V) [DecidableEq V] where
  /-- The underlying leaf/introduce/forget/join tree. -/
  tree : NiceTree V
  /-- Local validity of introduce, forget, and join operations. -/
  localValid : tree.LocalValid
  /-- The root bag is empty. -/
  bag_root : tree.bag = ∅
  /-- Every vertex appears in the tree. -/
  exists_mem_bag (v : V) : v ∈ tree.subtreeVerts
  /-- Every edge of `G` appears in some bag of the tree. -/
  exists_adj_mem_bag ⦃u v : V⦄ : G.Adj u v → tree.CoversFinset {u, v}

namespace NiceTreeDecomposition

variable [DecidableEq V] {G : SimpleGraph V}

/-- Width of a nice tree decomposition: largest bag size minus one. -/
@[expose] def width (N : G.NiceTreeDecomposition) : ℕ :=
  N.tree.width

/-- Number of nodes in a nice tree decomposition. -/
@[expose] def size (N : G.NiceTreeDecomposition) : ℕ :=
  N.tree.size

/-- Every finite clique of `G` lies in some bag of `N`. -/
theorem exists_coversFinset_of_isClique (N : G.NiceTreeDecomposition) {K : Finset V}
    (hK : G.IsClique (K : Set V)) : N.tree.CoversFinset K :=
  N.tree.exists_coversFinset_of_isClique N.localValid
    (fun _ _ huv _ _ => N.exists_adj_mem_bag huv) hK fun v _ => N.exists_mem_bag v

theorem width_le_iff (N : G.NiceTreeDecomposition) {k : ℕ} :
    N.width ≤ k ↔ N.tree.maxBagCard ≤ k + 1 :=
  NiceTree.width_le_iff

end NiceTreeDecomposition

end Bundled

/-! ### Converting `NiceTree` to `RootedTreeDecomposition` -/

namespace NiceTree

variable {V : Type uV} [DecidableEq V]

private def unaryRootedData (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V) :
    Fin (child.sizePred + 1 + 1) → Fin (child.sizePred + 1 + 1) × Finset V := fun i =>
  if _ : i.val = 0 then (0, rootBag)
  else
    let j : Fin (child.sizePred + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    let d := dChild j
    let p : Fin (child.sizePred + 1 + 1) :=
      if _ : j.val = 0 then 0 else ⟨d.1.val + 1, by have := d.1.isLt; omega⟩
    (p, d.2)

omit [DecidableEq V] in
private theorem unaryRootedData_zero (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V) :
    unaryRootedData rootBag child dChild 0 = (0, rootBag) := by
  simp [unaryRootedData]

omit [DecidableEq V] in
private theorem unaryRootedData_succ_bag (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    (k : Fin (child.sizePred + 1)) :
    (unaryRootedData rootBag child dChild ⟨1 + k.val, by have := k.isLt; omega⟩).2 =
      (dChild k).2 := by
  simp only [unaryRootedData, show 1 + k.val ≠ 0 by omega, ↓reduceDIte]
  have h : (⟨1 + k.val - 1, by have := k.isLt; omega⟩ : Fin (child.sizePred + 1)) = k :=
    Fin.ext (by dsimp; omega)
  rw [h]

omit [DecidableEq V] in
private theorem unaryRootedData_succ_bag_of_ne_zero (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    {i : Fin (child.sizePred + 1 + 1)} (hi0 : i.val ≠ 0) :
    (unaryRootedData rootBag child dChild i).2 =
      (dChild ⟨i.val - 1, by have := i.isLt; omega⟩).2 := by
  simp only [unaryRootedData, hi0, ↓reduceDIte]

omit [DecidableEq V] in
private theorem unaryRootedData_succ_parent_one (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V) :
    (unaryRootedData rootBag child dChild ⟨1, by omega⟩).1 = 0 := by
  simp [unaryRootedData]

omit [DecidableEq V] in
private theorem unaryRootedData_succ_parent_gt (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    {k : Fin (child.sizePred + 1)} (hk : k.val ≠ 0) :
    ((unaryRootedData rootBag child dChild ⟨1 + k.val, by have := k.isLt; omega⟩).1).val =
      1 + (dChild k).1.val := by
  have h1 : ((unaryRootedData rootBag child dChild ⟨1 + k.val, by have := k.isLt; omega⟩).1).val =
      if _ : (⟨1 + k.val - 1, by have := k.isLt; omega⟩ : Fin (child.sizePred + 1)).val = 0 then 0
      else (dChild ⟨1 + k.val - 1, by have := k.isLt; omega⟩).1.val + 1 := by
    simp only [unaryRootedData, show 1 + k.val ≠ 0 by omega, ↓reduceDIte]
    split_ifs <;> rfl
  rw [h1]
  have heq : (⟨1 + k.val - 1, by have := k.isLt; omega⟩ : Fin (child.sizePred + 1)) = k :=
    Fin.ext (by dsimp; omega)
  rw [heq, dite_eq_right (fun h0 => absurd h0 hk)]
  omega

/-- Pre-order parent and bag tables for `T : NiceTree V` indexed by `Fin (T.sizePred + 1)`. -/
private def rootedData : (T : NiceTree V) →
    Fin (T.sizePred + 1) → Fin (T.sizePred + 1) × Finset V
  | .leaf, _ => (0, ∅)
  | .introduce v child, i => unaryRootedData (insert v child.bag) child (rootedData child) i
  | .forget v child, i => unaryRootedData (child.bag.erase v) child (rootedData child) i
  | .join left right, i =>
    if _ : i.val = 0 then (0, left.bag)
    else if _ : i.val ≤ left.sizePred + 1 then
      let j : Fin (left.sizePred + 1) := ⟨i.val - 1, by omega⟩
      let d := rootedData left j
      let p : Fin (left.sizePred + right.sizePred + 2 + 1) :=
        if _ : j.val = 0 then 0 else ⟨d.1.val + 1, by have := d.1.isLt; omega⟩
      (p, d.2)
    else
      let j : Fin (right.sizePred + 1) := ⟨i.val - (left.sizePred + 1) - 1, by
        have := i.isLt; simp only [sizePred] at this; omega⟩
      let d := rootedData right j
      let p : Fin (left.sizePred + right.sizePred + 2 + 1) :=
        if _ : j.val = 0 then 0
        else ⟨left.sizePred + 2 + d.1.val, by have := d.1.isLt; omega⟩
      (p, d.2)

private theorem rootedData_parent_zero (T : NiceTree V) : (rootedData T 0).1 = 0 := by
  cases T with
  | leaf => rfl
  | introduce v child =>
    dsimp only [sizePred] at *
    change (unaryRootedData (insert v child.bag) child (rootedData child) 0).1 = 0
    rw [unaryRootedData_zero]
  | forget v child =>
    dsimp only [sizePred] at *
    change (unaryRootedData (child.bag.erase v) child (rootedData child) 0).1 = 0
    rw [unaryRootedData_zero]
  | join left right => simp [rootedData]

private theorem rootedData_bag_zero (T : NiceTree V) : (rootedData T 0).2 = T.bag := by
  cases T with
  | leaf => rfl
  | introduce v child =>
    dsimp only [sizePred] at *
    change (unaryRootedData (insert v child.bag) child (rootedData child) 0).2 = _
    rw [unaryRootedData_zero, bag]
  | forget v child =>
    dsimp only [sizePred] at *
    change (unaryRootedData (child.bag.erase v) child (rootedData child) 0).2 = _
    rw [unaryRootedData_zero, bag]
  | join left right => simp [rootedData, bag]

omit [DecidableEq V] in
private theorem unaryRootedData_parent_lt (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    (hchild : ∀ j : Fin (child.sizePred + 1), j.val ≠ 0 → (dChild j).1 < j)
    (i : Fin (child.sizePred + 1 + 1)) (hi : i.val ≠ 0) :
    (unaryRootedData rootBag child dChild i).1 < i := by
  simp only [unaryRootedData, hi, ↓reduceDIte]
  split_ifs with hj
  · exact Fin.lt_def.2 (by dsimp; omega)
  · have ih := hchild ⟨i.val - 1, by have := i.isLt; omega⟩ hj
    exact Fin.lt_def.2 (by dsimp; rw [Fin.lt_def] at ih; dsimp at ih; omega)

private theorem rootedData_parent_lt :
    ∀ (T : NiceTree V) (i : Fin (T.sizePred + 1)), i.val ≠ 0 → (rootedData T i).1 < i
  | .leaf, i, hi => by
    have h0 : i.val = 0 := by have := i.isLt; simp only [sizePred] at this; omega
    exact absurd h0 hi
  | .introduce v child, i, hi =>
    unaryRootedData_parent_lt _ child (rootedData child) (rootedData_parent_lt child) i hi
  | .forget v child, i, hi =>
    unaryRootedData_parent_lt _ child (rootedData child) (rootedData_parent_lt child) i hi
  | .join left right, i, hi => by
    dsimp only [sizePred] at i hi
    simp only [rootedData, hi, ↓reduceDIte]
    split_ifs with hL hj hj'
    · exact Fin.lt_def.2 (by dsimp; omega)
    · have ih := rootedData_parent_lt left ⟨i.val - 1, by omega⟩ hj
      exact Fin.lt_def.2 (by dsimp; rw [Fin.lt_def] at ih; dsimp at ih; omega)
    · exact Fin.lt_def.2 (by dsimp; omega)
    · have ih := rootedData_parent_lt right ⟨i.val - (left.sizePred + 1) - 1, by
        have := i.isLt; omega⟩ hj'
      exact Fin.lt_def.2 (by dsimp; rw [Fin.lt_def] at ih; dsimp at ih; omega)

private theorem mem_subtreeVerts_of_rootedData :
    ∀ {T : NiceTree V} {i : Fin (T.sizePred + 1)} {v : V},
      v ∈ (rootedData T i).2 → v ∈ T.subtreeVerts
  | .leaf, i, v, hv => by simp [rootedData] at hv
  | .introduce w child, i, v, hv => by
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero] at hv
      exact Finset.insert_subset_insert w child.bag_subset_subtreeVerts hv
    · have hv' : v ∈ (rootedData child
          ⟨i.val - 1, by have := i.isLt; simp only [sizePred] at this; omega⟩).2 := by
        rw [← unaryRootedData_succ_bag_of_ne_zero (insert w child.bag) child (rootedData child)
          hi0]
        exact hv
      exact Finset.mem_insert_of_mem (mem_subtreeVerts_of_rootedData (T := child) hv')
  | .forget w child, i, v, hv => by
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero] at hv
      exact ((Finset.erase_subset w _).trans child.bag_subset_subtreeVerts) hv
    · have hv' : v ∈ (rootedData child
          ⟨i.val - 1, by have := i.isLt; simp only [sizePred] at this; omega⟩).2 := by
        rw [← unaryRootedData_succ_bag_of_ne_zero (child.bag.erase w) child (rootedData child)
          hi0]
        exact hv
      exact mem_subtreeVerts_of_rootedData (T := child) hv'
  | .join left right, i, v, hv => by
    dsimp only [rootedData] at hv
    split_ifs at hv
    · exact Finset.mem_union_left _ (left.bag_subset_subtreeVerts hv)
    · exact Finset.mem_union_left _ (mem_subtreeVerts_of_rootedData (T := left) hv)
    · exact Finset.mem_union_left _ (mem_subtreeVerts_of_rootedData (T := left) hv)
    · exact Finset.mem_union_right _ (mem_subtreeVerts_of_rootedData (T := right) hv)
    · exact Finset.mem_union_right _ (mem_subtreeVerts_of_rootedData (T := right) hv)

private theorem join_left_bag (left right : NiceTree V) (k : Fin (left.sizePred + 1)) :
    (rootedData (.join left right)
      ⟨1 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).2 =
      (rootedData left k).2 := by
  have hkL : 1 + k.val ≤ left.sizePred + 1 := by have := k.isLt; omega
  dsimp only [rootedData]
  rw [dite_eq_right (by omega), dite_eq_left hkL]
  have heq : (⟨1 + k.val - 1, by omega⟩ : Fin (left.sizePred + 1)) = k := Fin.ext (by dsimp; omega)
  split_ifs <;> simp only [heq]

private theorem join_left_parent (left right : NiceTree V) {k : Fin (left.sizePred + 1)}
    (hk : k.val ≠ 0) :
    ((rootedData (.join left right)
      ⟨1 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).1).val =
      1 + ((rootedData left k).1).val := by
  have hkL : 1 + k.val ≤ left.sizePred + 1 := by have := k.isLt; omega
  have h1 : ((rootedData (.join left right)
      ⟨1 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).1).val =
      if _ : (⟨1 + k.val - 1, by omega⟩ : Fin (left.sizePred + 1)).val = 0 then (0 : ℕ)
      else ((rootedData left ⟨1 + k.val - 1, by omega⟩).1).val + 1 := by
    dsimp only [rootedData]
    rw [dite_eq_right (by omega), dite_eq_left hkL]
    split_ifs <;> rfl
  rw [h1]
  have heq : (⟨1 + k.val - 1, by omega⟩ : Fin (left.sizePred + 1)) = k := Fin.ext (by dsimp; omega)
  rw [heq, dite_eq_right (fun h0 => absurd h0 hk)]
  omega

private theorem join_right_bag (left right : NiceTree V) (k : Fin (right.sizePred + 1)) :
    (rootedData (.join left right)
      ⟨left.sizePred + 2 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).2 =
      (rootedData right k).2 := by
  have hnot : ¬(left.sizePred + 2 + k.val ≤ left.sizePred + 1) := by omega
  dsimp only [rootedData]
  rw [dite_eq_right (by omega), dite_eq_right hnot]
  have heq : (⟨left.sizePred + 2 + k.val - (left.sizePred + 1) - 1, by
      have := k.isLt; omega⟩ : Fin (right.sizePred + 1)) = k := Fin.ext (by dsimp; omega)
  split_ifs <;> simp only [heq]

private theorem join_right_parent (left right : NiceTree V) {k : Fin (right.sizePred + 1)}
    (hk : k.val ≠ 0) :
    ((rootedData (.join left right)
      ⟨left.sizePred + 2 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).1).val =
      left.sizePred + 2 + ((rootedData right k).1).val := by
  have hnot : ¬(left.sizePred + 2 + k.val ≤ left.sizePred + 1) := by omega
  have h1 : ((rootedData (.join left right)
      ⟨left.sizePred + 2 + k.val, by simp only [sizePred]; have := k.isLt; omega⟩).1).val =
      if _ : (⟨left.sizePred + 2 + k.val - (left.sizePred + 1) - 1, by
          have := k.isLt; omega⟩ : Fin (right.sizePred + 1)).val = 0 then (0 : ℕ)
      else left.sizePred + 2 + ((rootedData right
        ⟨left.sizePred + 2 + k.val - (left.sizePred + 1) - 1, by
          have := k.isLt; omega⟩).1).val := by
    dsimp only [rootedData]
    rw [dite_eq_right (by omega), dite_eq_right hnot]
    split_ifs <;> rfl
  rw [h1]
  have heq : (⟨left.sizePred + 2 + k.val - (left.sizePred + 1) - 1, by
      have := k.isLt; omega⟩ : Fin (right.sizePred + 1)) = k := Fin.ext (by dsimp; omega)
  rw [heq, dite_eq_right (fun h0 => absurd h0 hk)]

private theorem rootedData_coversFinset {T : NiceTree V} {K : Finset V}
    (h : T.CoversFinset K) : ∃ i : Fin (T.sizePred + 1), K ⊆ (rootedData T i).2 := by
  induction T with
  | leaf => exact ⟨0, h⟩
  | introduce w child ih =>
    rcases h with h | h
    · exact ⟨0, by rw [rootedData_bag_zero]; exact h⟩
    · obtain ⟨j, hj⟩ := ih h
      refine ⟨⟨1 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
      change K ⊆ (unaryRootedData (insert w child.bag) child (rootedData child) ⟨1 + j.val, _⟩).2
      rw [unaryRootedData_succ_bag]
      exact hj
  | forget w child ih =>
    rcases h with h | h
    · exact ⟨0, by rw [rootedData_bag_zero]; exact h⟩
    · obtain ⟨j, hj⟩ := ih h
      refine ⟨⟨1 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
      change K ⊆ (unaryRootedData (child.bag.erase w) child (rootedData child) ⟨1 + j.val, _⟩).2
      rw [unaryRootedData_succ_bag]
      exact hj
  | join left right ihL ihR =>
    rcases h with h | h | h
    · exact ⟨0, by rw [rootedData_bag_zero]; exact h⟩
    · obtain ⟨j, hj⟩ := ihL h
      exact ⟨⟨j.val + 1, by simp only [sizePred]; have := j.isLt; omega⟩, by
        rw [show (⟨j.val + 1, by simp only [sizePred]; have := j.isLt; omega⟩ :
            Fin ((left.join right).sizePred + 1)) =
            ⟨1 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩ from
          Fin.ext (by dsimp; omega), join_left_bag]
        exact hj⟩
    · obtain ⟨j, hj⟩ := ihR h
      have hnot : ¬(left.sizePred + 2 + j.val ≤ left.sizePred + 1) := by omega
      exact ⟨⟨left.sizePred + 2 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, by
        rw [join_right_bag]; exact hj⟩

private theorem rootedData_card_le_maxBagCard (T : NiceTree V) (i : Fin (T.sizePred + 1)) :
    (rootedData T i).2.card ≤ T.maxBagCard := by
  induction T with
  | leaf => simp [rootedData, maxBagCard]
  | introduce w child ih =>
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero, bag]
      exact le_max_left _ _
    · have his : i.val < child.sizePred + 1 + 1 := by
        have := i.isLt; simp only [sizePred] at this; exact this
      change (unaryRootedData (insert w child.bag) child (rootedData child) i).2.card ≤ _
      rw [unaryRootedData_succ_bag_of_ne_zero _ child (rootedData child) hi0]
      exact (ih ⟨i.val - 1, by omega⟩).trans (le_max_right _ _)
  | forget w child ih =>
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero, bag]
      exact le_max_left _ _
    · have his : i.val < child.sizePred + 1 + 1 := by
        have := i.isLt; simp only [sizePred] at this; exact this
      change (unaryRootedData (child.bag.erase w) child (rootedData child) i).2.card ≤ _
      rw [unaryRootedData_succ_bag_of_ne_zero _ child (rootedData child) hi0]
      exact (ih ⟨i.val - 1, by omega⟩).trans (le_max_right _ _)
  | join left right ihL ihR =>
    by_cases hi0 : i.val = 0
    · have hi' : i = 0 := Fin.ext hi0
      rw [hi', rootedData_bag_zero, bag]
      exact le_max_left _ _
    · by_cases hL : i.val ≤ left.sizePred + 1
      · dsimp only [rootedData]
        rw [dite_eq_right hi0, dite_eq_left hL]
        split_ifs
        · exact (ihL _).trans ((le_max_left _ _).trans (le_max_right _ _))
        · exact (ihL _).trans ((le_max_left _ _).trans (le_max_right _ _))
      · dsimp only [rootedData]
        rw [dite_eq_right hi0, dite_eq_right hL]
        split_ifs
        · exact (ihR _).trans ((le_max_right _ _).trans (le_max_right _ _))
        · exact (ihR _).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem exists_rootedData_card_eq_maxBagCard (T : NiceTree V) :
    ∃ i : Fin (T.sizePred + 1), T.maxBagCard ≤ (rootedData T i).2.card := by
  induction T with
  | leaf => exact ⟨0, by simp [rootedData, maxBagCard]⟩
  | introduce w child ih =>
    rcases le_total (insert w child.bag).card child.maxBagCard with h | h
    · obtain ⟨j, hj⟩ := ih
      refine ⟨⟨1 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
      change _ ≤
        (unaryRootedData (insert w child.bag) child (rootedData child) ⟨1 + j.val, _⟩).2.card
      rw [unaryRootedData_succ_bag]
      simpa only [maxBagCard, max_eq_right h] using hj
    · refine ⟨0, ?_⟩
      rw [rootedData_bag_zero]
      simp only [bag, maxBagCard, max_eq_left h, le_rfl]
  | forget w child ih =>
    rcases le_total (child.bag.erase w).card child.maxBagCard with h | h
    · obtain ⟨j, hj⟩ := ih
      refine ⟨⟨1 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
      change _ ≤
        (unaryRootedData (child.bag.erase w) child (rootedData child) ⟨1 + j.val, _⟩).2.card
      rw [unaryRootedData_succ_bag]
      simpa only [maxBagCard, max_eq_right h] using hj
    · refine ⟨0, ?_⟩
      rw [rootedData_bag_zero]
      simp only [bag, maxBagCard, max_eq_left h, le_rfl]
  | join left right ihL ihR =>
    rcases le_total left.maxBagCard right.maxBagCard with hLR | hLR
    · rcases le_total left.bag.card right.maxBagCard with hB | hB
      · obtain ⟨j, hj⟩ := ihR
        refine ⟨⟨left.sizePred + 2 + j.val, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
        simp only [maxBagCard, max_eq_right hLR, max_eq_right hB]
        rw [join_right_bag]
        exact hj
      · refine ⟨0, ?_⟩
        rw [rootedData_bag_zero]
        simp only [bag, maxBagCard, max_eq_right hLR, max_eq_left hB, le_rfl]
    · rcases le_total left.bag.card left.maxBagCard with hB | hB
      · obtain ⟨j, hj⟩ := ihL
        refine ⟨⟨j.val + 1, by simp only [sizePred]; have := j.isLt; omega⟩, ?_⟩
        have hjL : j.val + 1 ≤ left.sizePred + 1 := j.isLt
        simp only [rootedData, Nat.succ_ne_zero, ↓reduceDIte, hjL, maxBagCard, max_eq_left hLR,
          max_eq_right hB]
        exact hj
      · refine ⟨0, ?_⟩
        rw [rootedData_bag_zero]
        simp only [bag, maxBagCard, max_eq_left hLR, max_eq_left hB, le_rfl]

/-- Embed a child's induced bag-subtree into a parent `NiceTree`'s induced bag-subtree by
shifting indices by `off ≥ 1`. -/
private def shiftInduceHom {T C : NiceTree V} {v : V} (off : ℕ) (_ : 0 < off)
    (hlt : ∀ k : Fin (C.sizePred + 1), off + k.val < T.sizePred + 1)
    (hbag : ∀ k : Fin (C.sizePred + 1),
      (rootedData T ⟨off + k.val, hlt k⟩).2 = (rootedData C k).2)
    (hpar : ∀ k : Fin (C.sizePred + 1), k.val ≠ 0 →
      ((rootedData T ⟨off + k.val, hlt k⟩).1).val = off + ((rootedData C k).1).val) :
    (parentTree (fun k => (rootedData C k).1)).induce {k | v ∈ (rootedData C k).2} →g
      (parentTree (fun k => (rootedData T k).1)).induce {k | v ∈ (rootedData T k).2} where
  toFun k := ⟨⟨off + k.1.val, hlt k.1⟩, by
    change v ∈ (rootedData T ⟨off + k.1.val, hlt k.1⟩).2
    rw [hbag k.1]
    exact k.2⟩
  map_rel' {a b} hab := by
    change (parentTree (fun k => (rootedData C k).1)).Adj a.1 b.1 at hab
    change (parentTree (fun k => (rootedData T k).1)).Adj
      ⟨off + a.1.val, hlt a.1⟩ ⟨off + b.1.val, hlt b.1⟩
    rw [parentTree_adj (fun k hk => rootedData_parent_lt C k (Fin.val_ne_of_ne hk))] at hab
    rw [parentTree_adj (fun k hk => rootedData_parent_lt T k (Fin.val_ne_of_ne hk))]
    rcases hab with ⟨ha0, hpa⟩ | ⟨hb0, hpb⟩
    · left
      have ha0' : a.1.val ≠ 0 := fun h => ha0 (Fin.ext h)
      refine ⟨Fin.ne_of_val_ne (by dsimp; omega), Fin.ext ?_⟩
      dsimp
      rw [hpar a.1 ha0']
      exact congrArg (off + ·) (congrArg Fin.val hpa)
    · right
      have hb0' : b.1.val ≠ 0 := fun h => hb0 (Fin.ext h)
      refine ⟨Fin.ne_of_val_ne (by dsimp; omega), Fin.ext ?_⟩
      dsimp
      rw [hpar b.1 hb0']
      exact congrArg (off + ·) (congrArg Fin.val hpb)

private theorem reach_of_shift {T C : NiceTree V} {v : V} {off : ℕ} (hoff : 0 < off)
    (hlt : ∀ k : Fin (C.sizePred + 1), off + k.val < T.sizePred + 1)
    (hbag : ∀ k : Fin (C.sizePred + 1),
      (rootedData T ⟨off + k.val, hlt k⟩).2 = (rootedData C k).2)
    (hpar : ∀ k : Fin (C.sizePred + 1), k.val ≠ 0 →
      ((rootedData T ⟨off + k.val, hlt k⟩).1).val = off + ((rootedData C k).1).val)
    {j₁ j₂ : Fin (C.sizePred + 1)} {hj₁ : v ∈ (rootedData C j₁).2}
    {hj₂ : v ∈ (rootedData C j₂).2}
    (hreach : ((parentTree (fun k => (rootedData C k).1)).induce
      {k | v ∈ (rootedData C k).2}).Reachable ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩) :
    ((parentTree (fun k => (rootedData T k).1)).induce
      {k | v ∈ (rootedData T k).2}).Reachable
      ⟨⟨off + j₁.val, hlt j₁⟩, by change v ∈ (rootedData T _).2; rw [hbag j₁]; exact hj₁⟩
      ⟨⟨off + j₂.val, hlt j₂⟩, by change v ∈ (rootedData T _).2; rw [hbag j₂]; exact hj₂⟩ :=
  hreach.map (shiftInduceHom off hoff hlt hbag hpar)

private theorem reach_unary_root {T child : NiceTree V} {v : V} (hv : v ∈ T.bag)
    (hsize : T.sizePred = child.sizePred + 1)
    (hbag : ∀ k : Fin (child.sizePred + 1),
      (rootedData T ⟨1 + k.val, by have := k.isLt; omega⟩).2 = (rootedData child k).2)
    (hpar : ∀ k : Fin (child.sizePred + 1), k.val ≠ 0 →
      ((rootedData T ⟨1 + k.val, by have := k.isLt; omega⟩).1).val =
        1 + ((rootedData child k).1).val)
    (hpar1 : ((rootedData T ⟨1, by omega⟩).1).val = 0)
    (hvc : v ∈ child.bag) {i : Fin (T.sizePred + 1)} (hi0 : i.val ≠ 0)
    (hi : v ∈ (rootedData T i).2)
    (hc : ((parentTree (fun k => (rootedData child k).1)).induce
      {k | v ∈ (rootedData child k).2}).Reachable
      ⟨⟨i.val - 1, by have := i.isLt; omega⟩, by
        have hij : (⟨1 + (⟨i.val - 1, by have := i.isLt; omega⟩ :
            Fin (child.sizePred + 1)).val, by have := i.isLt; omega⟩ :
            Fin (T.sizePred + 1)) = i := Fin.ext (by dsimp; omega)
        change v ∈ (rootedData child _).2
        rw [← hbag, hij]
        exact hi⟩
      ⟨0, by change v ∈ (rootedData child 0).2; rw [rootedData_bag_zero]; exact hvc⟩) :
    ((parentTree (fun k => (rootedData T k).1)).induce
      {k | v ∈ (rootedData T k).2}).Reachable ⟨i, hi⟩
      ⟨0, by change v ∈ (rootedData T 0).2; rw [rootedData_bag_zero]; exact hv⟩ := by
  have hlt : ∀ k : Fin (child.sizePred + 1), 1 + k.val < T.sizePred + 1 := fun k => by
    have := k.isLt; omega
  have hr := reach_of_shift (by omega) hlt hbag hpar hc
  have hstep : ((parentTree (fun k => (rootedData T k).1)).induce
      {k | v ∈ (rootedData T k).2}).Adj
      ⟨⟨1 + (0 : Fin (child.sizePred + 1)).val, hlt 0⟩, by
        change v ∈ (rootedData T _).2; rw [hbag 0, rootedData_bag_zero]; exact hvc⟩
      ⟨0, by change v ∈ (rootedData T 0).2; rw [rootedData_bag_zero]; exact hv⟩ := by
    change (parentTree (fun k => (rootedData T k).1)).Adj ⟨1, hlt 0⟩ 0
    rw [parentTree_adj (fun k hk => rootedData_parent_lt T k (Fin.val_ne_of_ne hk))]
    left
    exact ⟨Fin.ne_of_val_ne (by dsimp; omega), Fin.ext hpar1⟩
  have hi_eq : (⟨i, hi⟩ : {k | v ∈ (rootedData T k).2}) =
      ⟨⟨1 + (i.val - 1), hlt ⟨i.val - 1, by have := i.isLt; omega⟩⟩, by
        have hij : (⟨1 + (i.val - 1), hlt ⟨i.val - 1, by have := i.isLt; omega⟩⟩ :
            Fin (T.sizePred + 1)) = i := Fin.ext (by dsimp; omega)
        change v ∈ (rootedData T ⟨1 + (i.val - 1), _⟩).2
        rw [hij]
        exact hi⟩ :=
    Subtype.ext (Fin.ext (by dsimp; omega))
  rw [hi_eq]
  exact hr.trans hstep.reachable

private theorem preconnected_unary_nonbag {T child : NiceTree V} {v : V}
    (hsize : T.sizePred = child.sizePred + 1)
    (hbag : ∀ k : Fin (child.sizePred + 1),
      (rootedData T ⟨1 + k.val, by have := k.isLt; omega⟩).2 = (rootedData child k).2)
    (hpar : ∀ k : Fin (child.sizePred + 1), k.val ≠ 0 →
      ((rootedData T ⟨1 + k.val, by have := k.isLt; omega⟩).1).val =
        1 + ((rootedData child k).1).val)
    (hv : v ∉ T.bag)
    (hc : ((parentTree (fun k => (rootedData child k).1)).induce
      {k | v ∈ (rootedData child k).2}).Preconnected)
    (a b : {k | v ∈ (rootedData T k).2}) :
    ((parentTree (fun k => (rootedData T k).1)).induce
      {k | v ∈ (rootedData T k).2}).Reachable a b := by
  have ha0 : a.1.val ≠ 0 := fun h0 => hv (by
    have ha' : a.1 = 0 := Fin.ext h0
    have h2 : v ∈ (rootedData T 0).2 := ha' ▸ a.2
    rwa [rootedData_bag_zero] at h2)
  have hb0 : b.1.val ≠ 0 := fun h0 => hv (by
    have hb' : b.1 = 0 := Fin.ext h0
    have h2 : v ∈ (rootedData T 0).2 := hb' ▸ b.2
    rwa [rootedData_bag_zero] at h2)
  have hlt : ∀ k : Fin (child.sizePred + 1), 1 + k.val < T.sizePred + 1 := fun k => by
    have := k.isLt; omega
  let ja : Fin (child.sizePred + 1) := ⟨a.1.val - 1, by have := a.1.isLt; omega⟩
  let jb : Fin (child.sizePred + 1) := ⟨b.1.val - 1, by have := b.1.isLt; omega⟩
  have hja : v ∈ (rootedData child ja).2 := by
    have hij : (⟨1 + ja.val, hlt ja⟩ : Fin (T.sizePred + 1)) = a.1 := Fin.ext (by dsimp [ja]; omega)
    rw [← hbag ja, hij]; exact a.2
  have hjb : v ∈ (rootedData child jb).2 := by
    have hij : (⟨1 + jb.val, hlt jb⟩ : Fin (T.sizePred + 1)) = b.1 := Fin.ext (by dsimp [jb]; omega)
    rw [← hbag jb, hij]; exact b.2
  have hr := reach_of_shift (by omega) hlt hbag hpar (hc ⟨ja, hja⟩ ⟨jb, hjb⟩)
  have ha_eq : a = ⟨⟨1 + ja.val, hlt ja⟩, by
      change v ∈ (rootedData T _).2; rw [hbag ja]; exact hja⟩ :=
    Subtype.ext (Fin.ext (by dsimp [ja]; omega))
  have hb_eq : b = ⟨⟨1 + jb.val, hlt jb⟩, by
      change v ∈ (rootedData T _).2; rw [hbag jb]; exact hjb⟩ :=
    Subtype.ext (Fin.ext (by dsimp [jb]; omega))
  rwa [ha_eq, hb_eq]

private theorem rootedData_preconnected_of_mem_bag :
    ∀ {T : NiceTree V} {v : V}, T.LocalValid → ∀ (hv : v ∈ T.bag)
      (i : Fin (T.sizePred + 1)) (hi : v ∈ (rootedData T i).2),
      ((parentTree (fun k => (rootedData T k).1)).induce
        {k | v ∈ (rootedData T k).2}).Reachable ⟨i, hi⟩
        ⟨0, by change v ∈ (rootedData T 0).2; rw [rootedData_bag_zero]; exact hv⟩
  | .leaf, _, _, _, i, _ => by
    have hi0 : i = 0 := Fin.eq_zero i
    subst hi0
    rfl
  | .introduce w child, v, hvalid, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · have : i = 0 := Fin.ext hi0; subst this; rfl
    · obtain ⟨hw_sub, hc⟩ := hvalid
      have hv_ne : v ≠ w := by
        intro hvw
        have his : i.val < child.sizePred + 1 + 1 := by
          have := i.isLt; simp only [sizePred] at this; exact this
        let k : Fin (child.sizePred + 1) := ⟨i.val - 1, by omega⟩
        have hik : (⟨1 + k.val, by have := k.isLt; omega⟩ : Fin (child.sizePred + 1 + 1)) = i :=
          Fin.ext (by dsimp [k]; omega)
        have hi' : w ∈ (rootedData child k).2 := by
          have hi'' : v ∈ (rootedData child k).2 := by
            rw [← unaryRootedData_succ_bag (insert w child.bag) child (rootedData child) k, hik]
            exact hi
          exact hvw ▸ hi''
        exact hw_sub (mem_subtreeVerts_of_rootedData hi')
      have hvc : v ∈ child.bag := (Finset.mem_insert.1 hv).resolve_left hv_ne
      exact reach_unary_root hv rfl
        (fun k => unaryRootedData_succ_bag _ _ _ k)
        (fun k hk => unaryRootedData_succ_parent_gt _ _ _ hk)
        (congrArg Fin.val (unaryRootedData_succ_parent_one _ _ _))
        hvc hi0 hi (rootedData_preconnected_of_mem_bag hc hvc _ _)
  | .forget w child, v, hvalid, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · have : i = 0 := Fin.ext hi0; subst this; rfl
    · obtain ⟨_, hc⟩ := hvalid
      have hvc : v ∈ child.bag := Finset.erase_subset w _ hv
      exact reach_unary_root hv rfl
        (fun k => unaryRootedData_succ_bag _ _ _ k)
        (fun k hk => unaryRootedData_succ_parent_gt _ _ _ hk)
        (congrArg Fin.val (unaryRootedData_succ_parent_one _ _ _))
        hvc hi0 hi (rootedData_preconnected_of_mem_bag hc hvc _ _)
  | .join left right, v, hvalid, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · have : i = 0 := Fin.ext hi0; subst this; rfl
    · obtain ⟨hbag, _, hcL, hcR⟩ := hvalid
      have hvL : v ∈ left.bag := hv
      have hvR : v ∈ right.bag := hbag ▸ hvL
      by_cases hL : i.val ≤ left.sizePred + 1
      · let j : Fin (left.sizePred + 1) := ⟨i.val - 1, by omega⟩
        have hlt : ∀ k : Fin (left.sizePred + 1), 1 + k.val < (join left right).sizePred + 1 :=
          fun k => by simp only [sizePred]; have := k.isLt; omega
        have hbagL := join_left_bag left right
        have hparL := fun k hk => join_left_parent left right (k := k) hk
        have hj : v ∈ (rootedData left j).2 := by
          have hij : (⟨1 + j.val, hlt j⟩ : Fin ((join left right).sizePred + 1)) = i :=
            Fin.ext (by dsimp [j]; omega)
          rw [← hbagL j, hij]; exact hi
        have hr := reach_of_shift (by omega) hlt hbagL hparL
          (rootedData_preconnected_of_mem_bag hcL hvL j hj)
        have hstep : ((parentTree (fun k => (rootedData (.join left right) k).1)).induce
            {k | v ∈ (rootedData (.join left right) k).2}).Adj
              ⟨⟨1 + (0 : Fin (left.sizePred + 1)).val, hlt 0⟩, by
                change v ∈ (rootedData (.join left right) _).2
                rw [hbagL 0, rootedData_bag_zero]; exact hvL⟩
              ⟨0, by change v ∈ (rootedData (.join left right) 0).2
                     rw [rootedData_bag_zero]; exact hv⟩ := by
          change (parentTree (fun k => (rootedData (.join left right) k).1)).Adj ⟨1, hlt 0⟩ 0
          rw [parentTree_adj (fun k hk => rootedData_parent_lt (.join left right) k
            (Fin.val_ne_of_ne hk))]
          left
          refine ⟨Fin.ne_of_val_ne (by dsimp; omega), ?_⟩
          apply Fin.ext
          dsimp only [sizePred, rootedData]
          rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_left rfl]
          rfl
        have hi_eq : (⟨i, hi⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨1 + j.val, hlt j⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbagL j]; exact hj⟩ :=
          Subtype.ext (Fin.ext (by dsimp [j]; omega))
        rw [hi_eq]
        exact hr.trans hstep.reachable
      · let j : Fin (right.sizePred + 1) := ⟨i.val - (left.sizePred + 1) - 1, by
          have := i.isLt; simp only [sizePred] at this; omega⟩
        have hlt : ∀ k : Fin (right.sizePred + 1),
            left.sizePred + 2 + k.val < (join left right).sizePred + 1 := fun k => by
          simp only [sizePred]; have := k.isLt; omega
        have hbagR := join_right_bag left right
        have hparR := fun k hk => join_right_parent left right (k := k) hk
        have hj : v ∈ (rootedData right j).2 := by
          have hij : (⟨left.sizePred + 2 + j.val, hlt j⟩ :
              Fin ((join left right).sizePred + 1)) = i := Fin.ext (by dsimp [j]; omega)
          rw [← hbagR j, hij]; exact hi
        have hr := reach_of_shift (by omega) hlt hbagR hparR
          (rootedData_preconnected_of_mem_bag hcR hvR j hj)
        have hstep : ((parentTree (fun k => (rootedData (.join left right) k).1)).induce
            {k | v ∈ (rootedData (.join left right) k).2}).Adj
              ⟨⟨left.sizePred + 2 + (0 : Fin (right.sizePred + 1)).val, hlt 0⟩, by
                change v ∈ (rootedData (.join left right) _).2
                rw [hbagR 0, rootedData_bag_zero]; exact hvR⟩
              ⟨0, by change v ∈ (rootedData (.join left right) 0).2
                     rw [rootedData_bag_zero]; exact hv⟩ := by
          change (parentTree (fun k => (rootedData (.join left right) k).1)).Adj
            ⟨left.sizePred + 2, hlt 0⟩ 0
          rw [parentTree_adj (fun k hk => rootedData_parent_lt (.join left right) k
            (Fin.val_ne_of_ne hk))]
          left
          refine ⟨Fin.ne_of_val_ne (by dsimp; omega), ?_⟩
          apply Fin.ext
          dsimp only [sizePred, rootedData]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
          rfl
        have hi_eq : (⟨i, hi⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨left.sizePred + 2 + j.val, hlt j⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbagR j]; exact hj⟩ :=
          Subtype.ext (Fin.ext (by dsimp [j]; omega))
        rw [hi_eq]
        exact hr.trans hstep.reachable

private theorem rootedData_preconnected :
    ∀ {T : NiceTree V} {v : V}, T.LocalValid →
      ((parentTree (fun k => (rootedData T k).1)).induce
        {k | v ∈ (rootedData T k).2}).Preconnected
  | .leaf, _, _ => by
    rintro ⟨a, _⟩ ⟨b, _⟩
    rw [Fin.eq_zero a, Fin.eq_zero b]
  | .introduce w child, v, hvalid => by
    rintro a b
    by_cases hv : v ∈ (NiceTree.introduce w child).bag
    · exact (rootedData_preconnected_of_mem_bag hvalid hv a.1 a.2).trans
        (rootedData_preconnected_of_mem_bag hvalid hv b.1 b.2).symm
    · exact preconnected_unary_nonbag rfl
        (fun k => by
          change (unaryRootedData (insert w child.bag) child (rootedData child)
            ⟨1 + k.val, _⟩).2 = (rootedData child k).2
          exact unaryRootedData_succ_bag _ _ _ k)
        (fun k hk => by
          change ((unaryRootedData (insert w child.bag) child (rootedData child)
            ⟨1 + k.val, _⟩).1).val = 1 + ((rootedData child k).1).val
          exact unaryRootedData_succ_parent_gt _ _ _ hk)
        hv (rootedData_preconnected hvalid.2) a b
  | .forget w child, v, hvalid => by
    rintro a b
    by_cases hv : v ∈ (NiceTree.forget w child).bag
    · exact (rootedData_preconnected_of_mem_bag hvalid hv a.1 a.2).trans
        (rootedData_preconnected_of_mem_bag hvalid hv b.1 b.2).symm
    · exact preconnected_unary_nonbag rfl
        (fun k => by
          change (unaryRootedData (child.bag.erase w) child (rootedData child)
            ⟨1 + k.val, _⟩).2 = (rootedData child k).2
          exact unaryRootedData_succ_bag _ _ _ k)
        (fun k hk => by
          change ((unaryRootedData (child.bag.erase w) child (rootedData child)
            ⟨1 + k.val, _⟩).1).val = 1 + ((rootedData child k).1).val
          exact unaryRootedData_succ_parent_gt _ _ _ hk)
        hv (rootedData_preconnected hvalid.2) a b
  | .join left right, v, hvalid => by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    by_cases hv : v ∈ (NiceTree.join left right).bag
    · exact (rootedData_preconnected_of_mem_bag hvalid hv a ha).trans
        (rootedData_preconnected_of_mem_bag hvalid hv b hb).symm
    · obtain ⟨_, hdisj, hcL, hcR⟩ := hvalid
      have ha0 : a.val ≠ 0 := fun h0 => hv (by
        have ha' : a = 0 := Fin.ext h0
        have h2 : v ∈ (rootedData (.join left right) 0).2 := ha' ▸ ha
        rwa [rootedData_bag_zero] at h2)
      have hb0 : b.val ≠ 0 := fun h0 => hv (by
        have hb' : b = 0 := Fin.ext h0
        have h2 : v ∈ (rootedData (.join left right) 0).2 := hb' ▸ hb
        rwa [rootedData_bag_zero] at h2)
      have hvL_not_or : ¬(v ∈ left.subtreeVerts ∧ v ∈ right.subtreeVerts) := fun ⟨hL, hR⟩ =>
        Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.2 ⟨hL, hv⟩) hR
      by_cases haL : a.val ≤ left.sizePred + 1 <;> by_cases hbL : b.val ≤ left.sizePred + 1
      · have hlt : ∀ k : Fin (left.sizePred + 1), 1 + k.val < (join left right).sizePred + 1 :=
          fun k => by simp only [sizePred]; have := k.isLt; omega
        have hbag := join_left_bag left right
        have hpar := fun k hk => join_left_parent left right (k := k) hk
        let ja : Fin (left.sizePred + 1) := ⟨a.val - 1, by omega⟩
        let jb : Fin (left.sizePred + 1) := ⟨b.val - 1, by omega⟩
        have hja : v ∈ (rootedData left ja).2 := by
          have hij : (⟨1 + ja.val, hlt ja⟩ : Fin ((join left right).sizePred + 1)) = a :=
            Fin.ext (by dsimp [ja]; omega)
          rw [← hbag ja, hij]; exact ha
        have hjb : v ∈ (rootedData left jb).2 := by
          have hij : (⟨1 + jb.val, hlt jb⟩ : Fin ((join left right).sizePred + 1)) = b :=
            Fin.ext (by dsimp [jb]; omega)
          rw [← hbag jb, hij]; exact hb
        have hr := reach_of_shift (by omega) hlt hbag hpar
          (rootedData_preconnected hcL ⟨ja, hja⟩ ⟨jb, hjb⟩)
        have ha_eq : (⟨a, ha⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨1 + ja.val, hlt ja⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbag ja]; exact hja⟩ :=
          Subtype.ext (Fin.ext (by dsimp [ja]; omega))
        have hb_eq : (⟨b, hb⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨1 + jb.val, hlt jb⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbag jb]; exact hjb⟩ :=
          Subtype.ext (Fin.ext (by dsimp [jb]; omega))
        rwa [ha_eq, hb_eq]
      · let ja : Fin (left.sizePred + 1) := ⟨a.val - 1, by omega⟩
        let jb : Fin (right.sizePred + 1) := ⟨b.val - (left.sizePred + 1) - 1, by
          have := b.isLt; simp only [sizePred] at this; omega⟩
        have hja : v ∈ (rootedData left ja).2 := by
          have hij : (⟨1 + ja.val, by simp only [sizePred]; omega⟩ :
              Fin ((join left right).sizePred + 1)) = a := Fin.ext (by dsimp [ja]; omega)
          rw [← join_left_bag left right ja, hij]; exact ha
        have hjb : v ∈ (rootedData right jb).2 := by
          have hij : (⟨left.sizePred + 2 + jb.val, by
              simp only [sizePred]; have := b.isLt; omega⟩ :
              Fin ((join left right).sizePred + 1)) = b := Fin.ext (by dsimp [jb]; omega)
          rw [← join_right_bag left right jb, hij]; exact hb
        exact absurd ⟨mem_subtreeVerts_of_rootedData hja, mem_subtreeVerts_of_rootedData hjb⟩
          hvL_not_or
      · let ja : Fin (right.sizePred + 1) := ⟨a.val - (left.sizePred + 1) - 1, by
          have := a.isLt; simp only [sizePred] at this; omega⟩
        let jb : Fin (left.sizePred + 1) := ⟨b.val - 1, by omega⟩
        have hjb : v ∈ (rootedData left jb).2 := by
          have hij : (⟨1 + jb.val, by simp only [sizePred]; omega⟩ :
              Fin ((join left right).sizePred + 1)) = b := Fin.ext (by dsimp [jb]; omega)
          rw [← join_left_bag left right jb, hij]; exact hb
        have hja : v ∈ (rootedData right ja).2 := by
          have hij : (⟨left.sizePred + 2 + ja.val, by
              simp only [sizePred]; have := a.isLt; omega⟩ :
              Fin ((join left right).sizePred + 1)) = a := Fin.ext (by dsimp [ja]; omega)
          rw [← join_right_bag left right ja, hij]; exact ha
        exact absurd ⟨mem_subtreeVerts_of_rootedData hjb, mem_subtreeVerts_of_rootedData hja⟩
          hvL_not_or
      · have hlt : ∀ k : Fin (right.sizePred + 1),
            left.sizePred + 2 + k.val < (join left right).sizePred + 1 := fun k => by
          simp only [sizePred]; have := k.isLt; omega
        have hbag := join_right_bag left right
        have hpar := fun k hk => join_right_parent left right (k := k) hk
        let ja : Fin (right.sizePred + 1) := ⟨a.val - (left.sizePred + 1) - 1, by
          have := a.isLt; simp only [sizePred] at this; omega⟩
        let jb : Fin (right.sizePred + 1) := ⟨b.val - (left.sizePred + 1) - 1, by
          have := b.isLt; simp only [sizePred] at this; omega⟩
        have hja : v ∈ (rootedData right ja).2 := by
          have hij : (⟨left.sizePred + 2 + ja.val, hlt ja⟩ :
              Fin ((join left right).sizePred + 1)) = a := Fin.ext (by dsimp [ja]; omega)
          rw [← hbag ja, hij]; exact ha
        have hjb : v ∈ (rootedData right jb).2 := by
          have hij : (⟨left.sizePred + 2 + jb.val, hlt jb⟩ :
              Fin ((join left right).sizePred + 1)) = b := Fin.ext (by dsimp [jb]; omega)
          rw [← hbag jb, hij]; exact hb
        have hr := reach_of_shift (by omega) hlt hbag hpar
          (rootedData_preconnected hcR ⟨ja, hja⟩ ⟨jb, hjb⟩)
        have ha_eq : (⟨a, ha⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨left.sizePred + 2 + ja.val, hlt ja⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbag ja]; exact hja⟩ :=
          Subtype.ext (Fin.ext (by dsimp [ja]; omega))
        have hb_eq : (⟨b, hb⟩ : {k | v ∈ (rootedData (.join left right) k).2}) =
            ⟨⟨left.sizePred + 2 + jb.val, hlt jb⟩, by
              change v ∈ (rootedData (.join left right) _).2; rw [hbag jb]; exact hjb⟩ :=
          Subtype.ext (Fin.ext (by dsimp [jb]; omega))
        rwa [ha_eq, hb_eq]

/-- Convert a valid `NiceTree` covering all vertices and edges of `G` into a
`RootedTreeDecomposition` with the same width and `T.size` nodes. -/
def toRootedTreeDecomposition {G : SimpleGraph V} (T : NiceTree V) (hvalid : T.LocalValid)
    (hvert : ∀ v : V, v ∈ T.subtreeVerts)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → T.CoversFinset {u, v}) :
    G.RootedTreeDecomposition T.sizePred where
  parent i := (rootedData T i).1
  parent_zero := rootedData_parent_zero T
  parent_lt i hi := rootedData_parent_lt T i (Fin.val_ne_of_ne hi)
  bag i := (rootedData T i).2
  exists_mem_bag v := by
    obtain ⟨i, hi⟩ := rootedData_coversFinset (coversFinset_singleton_of_mem_subtreeVerts (hvert v))
    exact ⟨i, hi (Finset.mem_singleton_self v)⟩
  exists_adj_mem_bag u v huv := by
    obtain ⟨i, hi⟩ := rootedData_coversFinset (hedge huv)
    exact ⟨i, hi (Finset.mem_insert_self u _),
      hi (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩
  top_unique v _ _ hi hit hj hjt :=
    eq_of_preconnected_parentTree (rootedData_parent_zero T)
      (fun i h => rootedData_parent_lt T i (Fin.val_ne_of_ne h))
      (rootedData_preconnected hvalid) hi hit hj hjt

theorem toRootedTreeDecomposition_width {G : SimpleGraph V} (T : NiceTree V) (hvalid : T.LocalValid)
    (hvert : ∀ v : V, v ∈ T.subtreeVerts)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → T.CoversFinset {u, v}) :
    (T.toRootedTreeDecomposition hvalid hvert hedge).width = T.width := by
  refine le_antisymm
    ((T.toRootedTreeDecomposition hvalid hvert hedge).width_le_iff.2 fun i => ?_) ?_
  · have hle := rootedData_card_le_maxBagCard T i
    change (rootedData T i).2.card ≤ T.width + 1
    dsimp only [width]
    omega
  · obtain ⟨i, hi⟩ := exists_rootedData_card_eq_maxBagCard T
    have hcard : (rootedData T i).2.card ≤
        (T.toRootedTreeDecomposition hvalid hvert hedge).width + 1 :=
      (T.toRootedTreeDecomposition hvalid hvert hedge).card_bag_le i
    dsimp only [width]
    omega

end NiceTree

namespace NiceTreeDecomposition

variable {V : Type uV} [DecidableEq V] {G : SimpleGraph V}

/-- Convert a bundled nice tree decomposition into a `RootedTreeDecomposition` of the same width
and `N.size` nodes. -/
def toRootedTreeDecomposition (N : G.NiceTreeDecomposition) :
    G.RootedTreeDecomposition N.tree.sizePred :=
  N.tree.toRootedTreeDecomposition N.localValid N.exists_mem_bag N.exists_adj_mem_bag

theorem toRootedTreeDecomposition_width (N : G.NiceTreeDecomposition) :
    N.toRootedTreeDecomposition.width = N.width :=
  N.tree.toRootedTreeDecomposition_width N.localValid N.exists_mem_bag N.exists_adj_mem_bag

end NiceTreeDecomposition

/-! ### Pruning redundant subset bags (`O(|V|)` nodes) -/

namespace RootedTreeDecomposition

variable {V : Type uV} {G : SimpleGraph V} [DecidableEq V]

private theorem succAbove_predAbove_of_ne {n : ℕ} {c x : Fin (n + 2)}
    (hc0 : c ≠ 0) (hx : x ≠ c) :
    c.succAbove ((c.pred hc0).predAbove x) = x := by
  have h1 := Fin.succ_succAbove_predAbove (p := c.pred hc0) (Fin.succ_pred c hc0 ▸ hx)
  rwa [Fin.succ_pred] at h1

/-- Contract a nonroot node `c` whose bag is a subset of its parent's bag, reducing the node
count by one without increasing the width. -/
def contractStep {n : ℕ} (R : G.RootedTreeDecomposition (n + 1)) (c : Fin (n + 2)) (hc0 : c ≠ 0)
    (hsub : R.bag c ⊆ R.bag (R.parent c)) : G.RootedTreeDecomposition n :=
  let drop : Fin (n + 2) → Fin (n + 1) := (c.pred hc0).predAbove
  let parent' : Fin (n + 1) → Fin (n + 1) := fun j =>
    let p := R.parent (c.succAbove j)
    drop (if p = c then R.parent c else p)
  have hzero : c.succAbove 0 = 0 := (Fin.succAbove_eq_zero_iff hc0).mpr rfl
  have hp0 : parent' 0 = 0 := by
    have h0 : R.parent (c.succAbove 0) = 0 := by rw [hzero, R.parent_zero]
    dsimp [parent', drop]
    rw [h0, ite_eq_right (fun h => absurd h hc0.symm)]
    exact Fin.succAbove_right_injective (p := c)
      (by rw [succAbove_predAbove_of_ne hc0 hc0.symm, hzero])
  have hplt : ∀ j : Fin (n + 1), j ≠ 0 → parent' j < j := by
    intro j hj0
    have hkne : c.succAbove j ≠ 0 := (Fin.succAbove_eq_zero_iff hc0).not.mpr hj0
    have hpk := R.parent_lt (c.succAbove j) hkne
    dsimp [parent', drop]
    rw [← Fin.succAbove_lt_succAbove_iff (p := c)]
    split_ifs with hpc
    · have hpc_lt := R.parent_lt c hc0
      rw [succAbove_predAbove_of_ne hc0 (ne_of_lt hpc_lt)]
      calc
        R.parent c < c := hpc_lt
        _ = R.parent (c.succAbove j) := hpc.symm
        _ < c.succAbove j := hpk
    · rwa [succAbove_predAbove_of_ne hc0 hpc]
  { parent := parent'
    parent_zero := hp0
    parent_lt := hplt
    bag := fun j => R.bag (c.succAbove j)
    exists_mem_bag := fun v => by
      obtain ⟨i, hi⟩ := R.exists_mem_bag v
      by_cases hic : i = c
      · have hpc : R.parent c ≠ c := ne_of_lt (R.parent_lt c hc0)
        exact ⟨drop (R.parent c), by
          rw [succAbove_predAbove_of_ne hc0 hpc]; exact hsub (hic ▸ hi)⟩
      · exact ⟨drop i, by rwa [succAbove_predAbove_of_ne hc0 hic]⟩
    exists_adj_mem_bag := fun u v huv => by
      obtain ⟨i, hu, hv⟩ := R.exists_adj_mem_bag huv
      by_cases hic : i = c
      · have hpc : R.parent c ≠ c := ne_of_lt (R.parent_lt c hc0)
        exact ⟨drop (R.parent c),
          by rw [succAbove_predAbove_of_ne hc0 hpc]; exact hsub (hic ▸ hu),
          by rw [succAbove_predAbove_of_ne hc0 hpc]; exact hsub (hic ▸ hv)⟩
      · exact ⟨drop i,
          by rw [succAbove_predAbove_of_ne hc0 hic]; exact hu,
          by rw [succAbove_predAbove_of_ne hc0 hic]; exact hv⟩
    top_unique := fun v _ _ hi hit hj hjt => by
      have htop_ne : R.top v ≠ c := by
        intro htc
        have htop := R.isTop_iff_mem.1 (R.isTop_top v)
        rw [htc] at htop
        rcases htop.2 with h0 | hnot
        · exact hc0 h0
        · exact hnot (hsub htop.1)
      let t' := drop (R.top v)
      have ht' : v ∈ R.bag (c.succAbove t') := by
        dsimp [t', drop]
        rw [succAbove_predAbove_of_ne hc0 htop_ne]
        exact R.mem_bag_top v
      have hreach : ∀ k : Fin (n + 2), ∀ j : Fin (n + 1), c.succAbove j = k →
          ∀ hj : v ∈ R.bag (c.succAbove j),
            ((parentTree parent').induce {m | v ∈ R.bag (c.succAbove m)}).Reachable
              ⟨j, hj⟩ ⟨t', ht'⟩ := by
        intro k
        induction k using WellFoundedLT.induction with
        | ind k ih =>
          intro j hjk hj
          subst hjk
          by_cases htopj : c.succAbove j = R.top v
          · have hjeq : j = t' := Fin.succAbove_right_injective (p := c)
              (by dsimp [t', drop]; rw [htopj, succAbove_predAbove_of_ne hc0 htop_ne])
            subst hjeq
            rfl
          · have hnot_top : ¬R.IsTop v (c.succAbove j) := fun h => htopj (R.isTop_iff.1 h)
            have hj0 : c.succAbove j ≠ 0 := by
              intro h0
              exact hnot_top (R.isTop_iff_mem.2 ⟨hj, Or.inl h0⟩)
            have hmem_p : v ∈ R.bag (R.parent (c.succAbove j)) := by
              by_contra hnot
              exact hnot_top (R.isTop_iff_mem.2 ⟨hj, Or.inr hnot⟩)
            have hpk : R.parent (c.succAbove j) < c.succAbove j := R.parent_lt _ hj0
            have hstep : ∀ (x : Fin (n + 2)) (hx_ne : x ≠ c) (hx_lt : x < c.succAbove j)
                (hx_mem : v ∈ R.bag x) (hpar : parent' j = drop x),
                ((parentTree parent').induce {m | v ∈ R.bag (c.succAbove m)}).Reachable
                  ⟨j, hj⟩ ⟨t', ht'⟩ := by
              intro x hx_ne hx_lt hx_mem hpar
              have hx'k : c.succAbove (drop x) = x := succAbove_predAbove_of_ne hc0 hx_ne
              have hx' : v ∈ R.bag (c.succAbove (drop x)) := by rwa [hx'k]
              have hadj : ((parentTree parent').induce {m | v ∈ R.bag (c.succAbove m)}).Adj
                  ⟨j, hj⟩ ⟨drop x, hx'⟩ := by
                change (parentTree parent').Adj j (drop x)
                rw [parentTree_adj hplt]
                left
                exact ⟨fun h0 => hj0 (by rw [h0, hzero]), hpar⟩
              exact hadj.reachable.trans (ih x hx_lt (drop x) hx'k hx')
            by_cases hpc : R.parent (c.succAbove j) = c
            · have hpc_lt : R.parent c < c := R.parent_lt c hc0
              have hpc_lt_j : R.parent c < c.succAbove j := by
                calc
                  R.parent c < c := hpc_lt
                  _ = R.parent (c.succAbove j) := hpc.symm
                  _ < c.succAbove j := hpk
              exact hstep (R.parent c) (ne_of_lt hpc_lt) hpc_lt_j
                (hsub (hpc ▸ hmem_p)) (by simp [parent', hpc])
            · exact hstep _ hpc hpk hmem_p (by simp [parent', hpc])
      exact eq_of_preconnected_parentTree hp0 hplt
        (fun ⟨a, ha⟩ ⟨b, hb⟩ => (hreach _ a rfl ha).trans (hreach _ b rfl hb).symm)
        hi hit hj hjt }

theorem contractStep_width_le {n : ℕ} (R : G.RootedTreeDecomposition (n + 1)) (c : Fin (n + 2))
    (hc0 : c ≠ 0) (hsub : R.bag c ⊆ R.bag (R.parent c)) :
    (R.contractStep c hc0 hsub).width ≤ R.width :=
  (width_le_iff _).2 fun j => by
    change (R.bag (c.succAbove j)).card ≤ R.width + 1
    exact R.card_bag_le _

/-- Iteratively contract all nonroot nodes whose bag is contained in their parent's bag. -/
def prune : ∀ {n : ℕ}, G.RootedTreeDecomposition n → Σ m : ℕ, G.RootedTreeDecomposition m
  | 0, R => ⟨0, R⟩
  | n + 1, R =>
    match h : (Finset.univ.filter fun c : Fin (n + 2) =>
        c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c)).min with
    | none => ⟨n + 1, R⟩
    | some c =>
      have hmem : c ∈ Finset.univ.filter fun c : Fin (n + 2) =>
          c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c) :=
        Finset.mem_of_min h
      have hc := (Finset.mem_filter.1 hmem).2
      prune (R.contractStep c hc.1 hc.2)

theorem prune_width_le : ∀ {n : ℕ} (R : G.RootedTreeDecomposition n), R.prune.2.width ≤ R.width
  | 0, R => le_rfl
  | n + 1, R => by
    conv_lhs => rw [prune]
    split
    · exact le_rfl
    · rename_i c h
      have hmem : c ∈ Finset.univ.filter fun c : Fin (n + 2) =>
          c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c) :=
        Finset.mem_of_min h
      have hc := (Finset.mem_filter.1 hmem).2
      exact (prune_width_le (R.contractStep c hc.1 hc.2)).trans
        (R.contractStep_width_le c hc.1 hc.2)

theorem not_subset_parent_of_prune :
    ∀ {n : ℕ} (R : G.RootedTreeDecomposition n) (c : Fin (R.prune.1 + 1)),
      c ≠ 0 → ¬R.prune.2.bag c ⊆ R.prune.2.bag (R.prune.2.parent c)
  | 0, R, c, hc => absurd (Fin.eq_zero c) hc
  | n + 1, R, c, hc => by
    revert c hc
    rw [prune]
    split <;> dsimp only at *
    · rename_i hnone
      intro c hc hsub
      have hmem : c ∈ Finset.univ.filter fun c : Fin (n + 2) =>
          c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, hsub⟩
      have := Finset.min_le hmem
      rw [hnone] at this
      exact absurd this (not_le_of_gt (WithTop.coe_lt_top _))
    · rename_i c' hsome
      intro c hc
      have hmem : c' ∈ Finset.univ.filter fun c : Fin (n + 2) =>
          c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c) :=
        Finset.mem_of_min hsome
      have hc' := (Finset.mem_filter.1 hmem).2
      exact not_subset_parent_of_prune (R.contractStep c' hc'.1 hc'.2) c hc

/-- When the vertex type `V` is finite, pruning leaves at most `card V + 1` nodes (`m ≤ card V`),
since every nonroot node introduces at least one vertex whose topmost node it is. -/
theorem prune_nodes_le [Fintype V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.prune.1 ≤ Fintype.card V := by
  classical
  let R' := R.prune.2
  let m := R.prune.1
  have hdiff : ∀ c : Fin (m + 1), c ≠ 0 → ∃ v : V, R'.top v = c := by
    intro c hc0
    obtain ⟨v, hvc, hvp⟩ := Finset.not_subset.1 (not_subset_parent_of_prune R c hc0)
    exact ⟨v, (R'.isTop_iff.1 (R'.isTop_iff_mem.2 ⟨hvc, Or.inr hvp⟩)).symm⟩
  let f : {c : Fin (m + 1) // c ≠ 0} → V := fun c => (hdiff c.1 c.2).choose
  have hinj : Function.Injective f := fun a b hab => by
    have ha := (hdiff a.1 a.2).choose_spec
    have hb := (hdiff b.1 b.2).choose_spec
    apply Subtype.ext
    rw [← ha, ← hb]
    exact congrArg R'.top hab
  have hcard := Fintype.card_le_of_injective f hinj
  have hsub : Fintype.card {c : Fin (m + 1) // c ≠ 0} = m := by
    simp [Fintype.card_subtype_compl]
  omega

end RootedTreeDecomposition

/-! ### Converting `RootedTreeDecomposition` and `TreeDecomposition` to `NiceTreeDecomposition` -/

namespace NiceTree

variable {V : Type uV} [DecidableEq V]

/-- Wrap `t` in a chain of `introduce` nodes for each element of `vs`. -/
@[expose] def introduceChain : List V → NiceTree V → NiceTree V
  | [], t => t
  | v :: vs, t => .introduce v (introduceChain vs t)

/-- Wrap `t` in a chain of `forget` nodes for each element of `vs`. -/
@[expose] def forgetChain : List V → NiceTree V → NiceTree V
  | [], t => t
  | v :: vs, t => .forget v (forgetChain vs t)

/-- Join a nonempty list of nice trees using binary `join` nodes. -/
@[expose] def joinTrees : NiceTree V → List (NiceTree V) → NiceTree V
  | t, [] => t
  | t, u :: us => .join t (joinTrees u us)

omit [DecidableEq V] in
private theorem size_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).size = vs.length + t.size := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih => simp only [introduceChain, size_introduce, ih, List.length_cons]; omega

omit [DecidableEq V] in
private theorem size_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).size = vs.length + t.size := by
  induction vs with
  | nil => simp [forgetChain]
  | cons v vs ih => simp only [forgetChain, size_forget, ih, List.length_cons]; omega

private theorem bag_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).bag = vs.toFinset ∪ t.bag := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih =>
    simp only [introduceChain, bag, ih, List.toFinset_cons, Finset.insert_union]

private theorem subtreeVerts_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).subtreeVerts = vs.toFinset ∪ t.subtreeVerts := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih =>
    simp only [introduceChain, subtreeVerts, ih, List.toFinset_cons, Finset.insert_union]

private theorem localValid_introduceChain {vs : List V} {t : NiceTree V}
    (hnd : vs.Nodup) (hdisj : ∀ v ∈ vs, v ∉ t.subtreeVerts) (ht : t.LocalValid) :
    (introduceChain vs t).LocalValid := by
  induction vs with
  | nil => exact ht
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    refine ⟨?_, ih hnd.2 (fun w hw => hdisj w (List.mem_cons_of_mem _ hw))⟩
    rw [subtreeVerts_introduceChain, Finset.mem_union, List.mem_toFinset]
    rintro (hv | hv)
    · exact hnd.1 hv
    · exact hdisj v List.mem_cons_self hv

private theorem maxBagCard_introduceChain_le (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).maxBagCard ≤ max (vs.toFinset ∪ t.bag).card t.maxBagCard := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih =>
    simp only [introduceChain, maxBagCard]
    refine max_le ?_ (ih.trans (max_le_max ?_ le_rfl))
    · have hsub : insert v (introduceChain vs t).bag ⊆ (v :: vs).toFinset ∪ t.bag := by
        rw [bag_introduceChain, List.toFinset_cons, Finset.insert_union]
      exact (Finset.card_le_card hsub).trans (le_max_left _ _)
    · exact Finset.card_le_card (Finset.union_subset_union_left (by
        rw [List.toFinset_cons]; exact Finset.subset_insert _ _))

private theorem coversFinset_introduceChain {vs : List V} {t : NiceTree V} {K : Finset V}
    (h : t.CoversFinset K) : (introduceChain vs t).CoversFinset K := by
  induction vs with
  | nil => exact h
  | cons v vs ih => exact Or.inr ih

private theorem bag_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).bag = t.bag \ vs.toFinset := by
  induction vs with
  | nil => simp [forgetChain]
  | cons v vs ih =>
    simp only [forgetChain, bag, ih, List.toFinset_cons]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

private theorem subtreeVerts_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).subtreeVerts = t.subtreeVerts := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [forgetChain, subtreeVerts, ih]

private theorem localValid_forgetChain {vs : List V} {t : NiceTree V}
    (hnd : vs.Nodup) (hsub : ∀ v ∈ vs, v ∈ t.bag) (ht : t.LocalValid) :
    (forgetChain vs t).LocalValid := by
  induction vs with
  | nil => exact ht
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    refine ⟨?_, ih hnd.2 (fun w hw => hsub w (List.mem_cons_of_mem _ hw))⟩
    rw [bag_forgetChain, Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨hsub v List.mem_cons_self, hnd.1⟩

private theorem maxBagCard_forgetChain_le (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).maxBagCard ≤ t.maxBagCard := by
  induction vs with
  | nil => exact le_rfl
  | cons v vs ih =>
    simp only [forgetChain, maxBagCard]
    refine max_le ?_ ih
    have hsub : (forgetChain vs t).bag.erase v ⊆ t.bag := by
      rw [bag_forgetChain]
      exact (Finset.erase_subset v _).trans Finset.sdiff_subset
    exact (Finset.card_le_card hsub).trans t.card_bag_le_maxBagCard

private theorem coversFinset_forgetChain {vs : List V} {t : NiceTree V} {K : Finset V}
    (h : t.CoversFinset K) : (forgetChain vs t).CoversFinset K := by
  induction vs with
  | nil => exact h
  | cons v vs ih => exact Or.inr ih

private theorem bag_joinTrees (t : NiceTree V) (ts : List (NiceTree V)) :
    (joinTrees t ts).bag = t.bag := by
  cases ts with
  | nil => rfl
  | cons u us => simp [joinTrees, bag]

private theorem mem_subtreeVerts_joinTrees {t : NiceTree V} {ts : List (NiceTree V)} {v : V} :
    v ∈ (joinTrees t ts).subtreeVerts ↔ v ∈ t.subtreeVerts ∨ ∃ u ∈ ts, v ∈ u.subtreeVerts := by
  induction ts generalizing t with
  | nil => simp [joinTrees]
  | cons u us ih =>
    simp only [joinTrees, subtreeVerts, Finset.mem_union, ih (t := u), List.mem_cons,
      exists_eq_or_imp]

private theorem maxBagCard_joinTrees_le (t : NiceTree V) (ts : List (NiceTree V))
    (hbags : ∀ u ∈ ts, u.bag = t.bag) :
    (joinTrees t ts).maxBagCard ≤ max t.maxBagCard ((ts.map maxBagCard).foldr max 0) := by
  induction ts generalizing t with
  | nil => simp [joinTrees]
  | cons u us ih =>
    have hus : ∀ w ∈ us, w.bag = u.bag := fun w hw =>
      (hbags w (List.mem_cons_of_mem _ hw)).trans (hbags u List.mem_cons_self).symm
    have ihu := ih (t := u) hus
    simp only [joinTrees, maxBagCard, List.map_cons, List.foldr_cons]
    refine max_le (t.card_bag_le_maxBagCard.trans (le_max_left _ _)) (max_le (le_max_left _ _) ?_)
    exact ihu.trans (max_le ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)))

omit [DecidableEq V] in
private theorem size_joinTrees (t : NiceTree V) (ts : List (NiceTree V)) :
    (joinTrees t ts).size = t.size + ts.length + (ts.map size).sum := by
  induction ts generalizing t with
  | nil => simp [joinTrees]
  | cons u us ih =>
    simp only [joinTrees, size_join, ih u, List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem localValid_joinTrees {B : Finset V} :
    ∀ (t : NiceTree V) (ts : List (NiceTree V)),
      t.bag = B → (∀ u ∈ ts, u.bag = B) →
      t.LocalValid → (∀ u ∈ ts, u.LocalValid) →
      (t :: ts).Pairwise (fun u w => Disjoint (u.subtreeVerts \ B) w.subtreeVerts) →
      (joinTrees t ts).LocalValid
  | t, [], _, _, ht, _, _ => ht
  | t, u :: us, hBt, hBus, ht, hLus, hpair => by
    rw [List.pairwise_cons] at hpair
    have hBu : u.bag = B := hBus u List.mem_cons_self
    have hjoin_bag : (joinTrees u us).bag = B := (bag_joinTrees u us).trans hBu
    have hvalidR : (joinTrees u us).LocalValid :=
      localValid_joinTrees u us hBu (fun w hw => hBus w (List.mem_cons_of_mem _ hw))
        (hLus u List.mem_cons_self) (fun w hw => hLus w (List.mem_cons_of_mem _ hw)) hpair.2
    refine ⟨hBt.trans hjoin_bag.symm, ?_, ht, hvalidR⟩
    rw [Finset.disjoint_left]
    intro x hxt hxj
    rw [hBt] at hxt
    rcases mem_subtreeVerts_joinTrees.1 hxj with hxu | ⟨w, hw, hxw⟩
    · exact Finset.disjoint_left.1 (hpair.1 u List.mem_cons_self) hxt hxu
    · exact Finset.disjoint_left.1 (hpair.1 w (List.mem_cons_of_mem _ hw)) hxt hxw

private theorem coversFinset_joinTrees {t : NiceTree V} {ts : List (NiceTree V)} {K : Finset V}
    (h : t.CoversFinset K ∨ ∃ u ∈ ts, u.CoversFinset K) : (joinTrees t ts).CoversFinset K := by
  induction ts generalizing t with
  | nil =>
    rcases h with h | ⟨u, hu, -⟩
    · exact h
    · exact absurd hu List.not_mem_nil
  | cons u us ih =>
    rcases h with h | ⟨w, hw, hcov⟩
    · exact Or.inr (Or.inl h)
    · rcases List.mem_cons.1 hw with rfl | hwu
      · exact Or.inr (Or.inr (ih (Or.inl hcov)))
      · exact Or.inr (Or.inr (ih (Or.inr ⟨w, hwu, hcov⟩)))

end NiceTree

namespace RootedTreeDecomposition

open NiceTree

variable {V : Type uV} {G : SimpleGraph V} [DecidableEq V]

/-- Wrap a converted child subtree `sub` of `c` into the forget/introduce step matching bag `i`. -/
private def niceStep (toList : Finset V → List V) {n : ℕ} (R : G.RootedTreeDecomposition n)
    (i c : Fin (n + 1)) (sub : NiceTree V) : NiceTree V :=
  introduceChain (toList (R.bag i \ R.bag c)) (forgetChain (toList (R.bag c \ R.bag i)) sub)

/-- Subtree conversion from node `i` using an explicit duplicate-free list enumerator `toList` for
`Finset V`. -/
private def toNiceSubtreeCore (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) : NiceTree V :=
  let cs := (R.children i).sort (· ≤ ·)
  if hcs : cs = [] then
    introduceChain (toList (R.bag i)) .leaf
  else
    let branches := cs.pmap (fun c hc =>
      have hmem : c ∈ R.children i := (Finset.mem_sort _).1 hc
      have _hlt : n - c.val < n - i.val := by
        have := R.lt_of_mem_children hmem
        rw [Fin.lt_def] at this
        have hc_le : c.val ≤ n := Nat.lt_succ_iff.1 c.isLt
        omega
      niceStep toList R i c (toNiceSubtreeCore toList R c)) (fun _ hc => hc)
    match hbr : branches with
    | b :: bs => joinTrees b bs
    | [] => by
      have hlen : cs.length = 0 := by
        calc
          cs.length = branches.length := List.length_pmap.symm
          _ = 0 := by rw [hbr, List.length_nil]
      exact absurd (List.eq_nil_of_length_eq_zero hlen) hcs
termination_by n - i.val

private theorem toNiceSubtreeCore_eq_joinTrees (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) (i : Fin (n + 1))
    (hcs : (R.children i).sort (· ≤ ·) ≠ [])
    {b : NiceTree V} {bs : List (NiceTree V)}
    (hbr : ((R.children i).sort (· ≤ ·)).pmap (fun c _ =>
      niceStep toList R i c (toNiceSubtreeCore toList R c)) (fun _ hc => hc) = b :: bs) :
    toNiceSubtreeCore toList R i = joinTrees b bs := by
  conv_lhs => rw [toNiceSubtreeCore]
  rw [dite_eq_right hcs]
  dsimp only
  split
  · rename_i b' bs' heq
    have hEq : b :: bs = b' :: bs' := hbr.symm.trans heq
    injection hEq with hb hbs
    rw [hb, hbs]
  · rename_i heq
    exact absurd (hbr.symm.trans heq) (List.cons_ne_nil b bs)

/-- Convert a rooted tree decomposition to a nice tree decomposition using `toList` to order
each bag or difference finset. -/
private def toNiceCore (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) : NiceTree V :=
  forgetChain (toList (R.bag 0)) (toNiceSubtreeCore toList R 0)

private structure ListSpec (toList : Finset V → List V) : Prop where
  nodup : ∀ S, (toList S).Nodup
  mem : ∀ S v, v ∈ toList S ↔ v ∈ S

private theorem toFinset_of_listSpec {toList : Finset V → List V} (hs : ListSpec toList)
    (S : Finset V) : (toList S).toFinset = S := by
  ext v
  simp only [List.mem_toFinset, hs.mem]

omit [DecidableEq V] in
private theorem length_le_card_of_listSpec {toList : Finset V → List V} (hs : ListSpec toList)
    (S : Finset V) : (toList S).length ≤ S.card := by
  classical
  have hsub : (toList S).toFinset = S := by
    ext v
    simp only [List.mem_toFinset, hs.mem]
  rw [← List.toFinset_card_of_nodup (hs.nodup S), hsub]

omit [DecidableEq V] in
private theorem foldr_max_le_of_forall {α : Type*} (f : α → ℕ) (k : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ k) → (l.map f).foldr max 0 ≤ k
  | [], _ => Nat.zero_le k
  | x :: xs, hx => max_le (hx x List.mem_cons_self)
      (foldr_max_le_of_forall f k xs fun y hy => hx y (List.mem_cons_of_mem _ hy))

private theorem toNiceSubtreeCore_props (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    (toNiceSubtreeCore toList R i).bag = R.bag i ∧
      (toNiceSubtreeCore toList R i).subtreeVerts = R.subtreeVerts i ∧
      (toNiceSubtreeCore toList R i).LocalValid ∧
      (toNiceSubtreeCore toList R i).maxBagCard ≤ R.width + 1 ∧
      (∀ j, R.IsDescendant j i → (toNiceSubtreeCore toList R i).CoversFinset (R.bag j)) := by
  by_cases hcs : (R.children i).sort (· ≤ ·) = []
  · rw [toNiceSubtreeCore, dite_eq_left hcs]
    have hno : ∀ c, c ∉ R.children i := by
      intro c hc
      have : c ∈ (R.children i).sort (· ≤ ·) := (Finset.mem_sort _).2 hc
      rw [hcs] at this
      exact absurd this List.not_mem_nil
    have hsub_eq : R.subtreeVerts i = R.bag i := by
      refine Finset.Subset.antisymm (fun v hv => ?_) (R.bag_subset_subtreeVerts i)
      by_contra hvi
      obtain ⟨c, hc, -⟩ := R.exists_mem_children_of_mem_subtreeVerts hv hvi
      exact hno c hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [bag_introduceChain, toFinset_of_listSpec hs]
      change (R.bag i) ∪ ∅ = R.bag i
      exact Finset.union_empty _
    · rw [subtreeVerts_introduceChain, toFinset_of_listSpec hs]
      change (R.bag i) ∪ ∅ = R.subtreeVerts i
      rw [Finset.union_empty, hsub_eq]
    · exact localValid_introduceChain (hs.nodup _) (fun _ _ => Finset.notMem_empty _) trivial
    · refine (maxBagCard_introduceChain_le _ _).trans (max_le ?_ (Nat.zero_le _))
      simp only [toFinset_of_listSpec hs]
      change (R.bag i ∪ ∅).card ≤ R.width + 1
      rw [Finset.union_empty]
      exact R.card_bag_le i
    · intro j hj
      by_cases hji : j = i
      · subst hji
        refine coversFinset_of_subset_bag ?_
        rw [bag_introduceChain, toFinset_of_listSpec hs]
        exact Finset.subset_union_left
      · obtain ⟨c, hc, -⟩ := exists_mem_children_of_isDescendant hj hji
        exact absurd hc (hno c)
  · set cs := (R.children i).sort (· ≤ ·)
    let br : Fin (n + 1) → NiceTree V := fun c =>
      niceStep toList R i c (toNiceSubtreeCore toList R c)
    have hih : ∀ (c : Fin (n + 1)), c ∈ R.children i →
        (br c).bag = R.bag i ∧
          (br c).subtreeVerts = R.bag i ∪ R.subtreeVerts c ∧
          (br c).LocalValid ∧
          (br c).maxBagCard ≤ R.width + 1 ∧
          (∀ j, R.IsDescendant j c → (br c).CoversFinset (R.bag j)) := by
      intro c hc
      have _hlt : n - c.val < n - i.val := by
        have := R.lt_of_mem_children hc
        rw [Fin.lt_def] at this
        have hc_le : c.val ≤ n := Nat.lt_succ_iff.1 c.isLt
        omega
      obtain ⟨hbag, hsub, hloc, hmax, hcov⟩ := toNiceSubtreeCore_props toList hs R c
      have hsub1 : (forgetChain (toList (R.bag c \ R.bag i))
          (toNiceSubtreeCore toList R c)).bag = R.bag c ∩ R.bag i := by
        rw [bag_forgetChain, hbag, toFinset_of_listSpec hs]
        ext v; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have hsub2 : (br c).bag = R.bag i := by
        dsimp [br, niceStep]
        rw [bag_introduceChain, hsub1, toFinset_of_listSpec hs]
        ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
      have hsv : (br c).subtreeVerts = R.bag i ∪ R.subtreeVerts c := by
        dsimp [br, niceStep]
        rw [subtreeVerts_introduceChain, subtreeVerts_forgetChain, hsub, toFinset_of_listSpec hs]
        ext v
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (⟨hvi, -⟩ | hvc)
          · exact Or.inl hvi
          · exact Or.inr hvc
        · rintro (hvi | hvc)
          · by_cases hvc' : v ∈ R.bag c
            · exact Or.inr (R.bag_subset_subtreeVerts c hvc')
            · exact Or.inl ⟨hvi, hvc'⟩
          · exact Or.inr hvc
      have hloc1 : (forgetChain (toList (R.bag c \ R.bag i))
          (toNiceSubtreeCore toList R c)).LocalValid :=
        localValid_forgetChain (hs.nodup _) (fun v hv => by
          rw [hs.mem] at hv
          rw [hbag]
          exact (Finset.mem_sdiff.1 hv).1) hloc
      have hloc2 : (br c).LocalValid :=
        localValid_introduceChain (hs.nodup _) (fun v hv => by
          rw [hs.mem] at hv
          rw [subtreeVerts_forgetChain, hsub]
          have hmem := Finset.mem_sdiff.1 hv
          intro hvc
          have hpc : v ∈ R.bag (R.parent c) := by
            rw [(mem_children.1 hc).2]
            exact hmem.1
          exact hmem.2 (R.mem_bag_of_mem_subtreeVerts_of_mem_bag_parent hvc hpc)) hloc1
      have hmax1 : (forgetChain (toList (R.bag c \ R.bag i))
          (toNiceSubtreeCore toList R c)).maxBagCard ≤ R.width + 1 :=
        (maxBagCard_forgetChain_le _ _).trans hmax
      have hmax2 : (br c).maxBagCard ≤ R.width + 1 := by
        refine (maxBagCard_introduceChain_le _ _).trans (max_le ?_ hmax1)
        rw [hsub1, toFinset_of_listSpec hs]
        have heq : (R.bag i \ R.bag c) ∪ (R.bag c ∩ R.bag i) = R.bag i := by
          ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
        rw [heq]
        exact R.card_bag_le i
      refine ⟨hsub2, hsv, hloc2, hmax2, fun j hj => ?_⟩
      exact coversFinset_introduceChain (coversFinset_forgetChain (hcov j hj))
    let branches := cs.pmap (fun c _ => br c) (fun _ hc => hc)
    have hbr_mem : ∀ c, c ∈ cs → br c ∈ branches := fun c hc =>
      List.mem_pmap.2 ⟨c, hc, rfl⟩
    have hmem_br : ∀ t ∈ branches, ∃ c, c ∈ cs ∧ t = br c := by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := List.mem_pmap.1 ht
      exact ⟨c, hc, rfl⟩
    have hpair_cs : cs.Pairwise (fun c₁ c₂ => c₁ ≠ c₂) := by
      rw [← List.nodup_iff_pairwise_ne]
      exact (R.children i).sort_nodup _
    have hpair_br : branches.Pairwise (fun u w =>
        Disjoint (u.subtreeVerts \ R.bag i) w.subtreeVerts) := by
      refine List.Pairwise.pmap hpair_cs (fun _ hc => hc) fun c₁ hc₁ c₂ hc₂ hne => ?_
      have hc₁' := (Finset.mem_sort _).1 hc₁
      have hc₂' := (Finset.mem_sort _).1 hc₂
      change Disjoint ((br c₁).subtreeVerts \ R.bag i) (br c₂).subtreeVerts
      rw [(hih c₁ hc₁').2.1, (hih c₂ hc₂').2.1, Finset.disjoint_left]
      intro v hv₁ hv₂
      rw [Finset.mem_sdiff, Finset.mem_union] at hv₁
      rw [Finset.mem_union] at hv₂
      have hv1 : v ∈ R.subtreeVerts c₁ := hv₁.1.resolve_left hv₁.2
      have hv2 : v ∈ R.subtreeVerts c₂ := hv₂.resolve_left hv₁.2
      exact hne (R.eq_of_mem_subtreeVerts_of_mem_children hc₁' hc₂' hv1 hv2 hv₁.2)
    cases hbr : branches with
    | nil =>
      have : cs.length = 0 := by
        have := congrArg List.length hbr
        simpa [branches] using this
      exact absurd (List.eq_nil_of_length_eq_zero this) hcs
    | cons b bs =>
      have hpair_cons : (b :: bs).Pairwise (fun u w =>
          Disjoint (u.subtreeVerts \ R.bag i) w.subtreeVerts) := by
        simpa [hbr] using hpair_br
      have hb_in : b ∈ branches := by rw [hbr]; exact List.mem_cons_self
      obtain ⟨c₀, hc₀, rfl⟩ := hmem_br b hb_in
      have hc₀' := (Finset.mem_sort _).1 hc₀
      have hbag_all : ∀ u ∈ bs, u.bag = R.bag i := fun u hu => by
        have hu' : u ∈ branches := by rw [hbr]; exact List.mem_cons_of_mem _ hu
        obtain ⟨c, hc, rfl⟩ := hmem_br u hu'
        exact (hih c ((Finset.mem_sort _).1 hc)).1
      have hloc_all : ∀ u ∈ bs, u.LocalValid := fun u hu => by
        have hu' : u ∈ branches := by rw [hbr]; exact List.mem_cons_of_mem _ hu
        obtain ⟨c, hc, rfl⟩ := hmem_br u hu'
        exact (hih c ((Finset.mem_sort _).1 hc)).2.2.1
      have hmax_all : ∀ u ∈ bs, u.maxBagCard ≤ R.width + 1 := fun u hu => by
        have hu' : u ∈ branches := by rw [hbr]; exact List.mem_cons_of_mem _ hu
        obtain ⟨c, hc, rfl⟩ := hmem_br u hu'
        exact (hih c ((Finset.mem_sort _).1 hc)).2.2.2.1
      have hbag_b : (br c₀).bag = R.bag i := (hih c₀ hc₀').1
      have hres_bag : (joinTrees (br c₀) bs).bag = R.bag i :=
        (bag_joinTrees _ bs).trans hbag_b
      have hres_sv : (joinTrees (br c₀) bs).subtreeVerts = R.subtreeVerts i := by
        refine Finset.Subset.antisymm (fun v hv => ?_) (fun v hv => ?_)
        · rcases mem_subtreeVerts_joinTrees.1 hv with hvb | ⟨u, hu, hvu⟩
          · rw [(hih c₀ hc₀').2.1] at hvb
            rcases Finset.mem_union.1 hvb with hvi | hvc
            · exact R.bag_subset_subtreeVerts i hvi
            · exact R.subtreeVerts_subset_of_mem_children hc₀' hvc
          · have hu' : u ∈ branches := by rw [hbr]; exact List.mem_cons_of_mem _ hu
            obtain ⟨c, hc, rfl⟩ := hmem_br u hu'
            have hc' := (Finset.mem_sort _).1 hc
            rw [(hih c hc').2.1] at hvu
            rcases Finset.mem_union.1 hvu with hvi | hvc
            · exact R.bag_subset_subtreeVerts i hvi
            · exact R.subtreeVerts_subset_of_mem_children hc' hvc
        · by_cases hvi : v ∈ R.bag i
          · exact mem_subtreeVerts_joinTrees.2 (Or.inl (by
              rw [(hih c₀ hc₀').2.1]; exact Finset.mem_union_left _ hvi))
          · obtain ⟨c, hc, hvc⟩ := R.exists_mem_children_of_mem_subtreeVerts hv hvi
            have hc_mem : c ∈ cs := (Finset.mem_sort (· ≤ ·)).2 hc
            have hbc : br c ∈ branches := hbr_mem c hc_mem
            rw [hbr, List.mem_cons] at hbc
            rcases hbc with hbc | hbc
            · exact mem_subtreeVerts_joinTrees.2 (Or.inl (by
                rw [← hbc, (hih c hc).2.1]; exact Finset.mem_union_right _ hvc))
            · exact mem_subtreeVerts_joinTrees.2 (Or.inr ⟨br c, hbc, by
                rw [(hih c hc).2.1]; exact Finset.mem_union_right _ hvc⟩)
      have hres_loc : (joinTrees (br c₀) bs).LocalValid :=
        localValid_joinTrees (br c₀) bs hbag_b hbag_all (hih c₀ hc₀').2.2.1 hloc_all hpair_cons
      have hres_max : (joinTrees (br c₀) bs).maxBagCard ≤ R.width + 1 :=
        (maxBagCard_joinTrees_le _ bs (fun u hu => (hbag_all u hu).trans hbag_b.symm)).trans
          (max_le (hih c₀ hc₀').2.2.2.1 (foldr_max_le_of_forall maxBagCard (R.width + 1) bs
            hmax_all))
      have hres_cov : ∀ j, R.IsDescendant j i →
          (joinTrees (br c₀) bs).CoversFinset (R.bag j) := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          exact coversFinset_of_subset_bag (by rw [hres_bag])
        · obtain ⟨c, hc, hjc⟩ := exists_mem_children_of_isDescendant hj hji
          have hc_mem : c ∈ cs := (Finset.mem_sort (· ≤ ·)).2 hc
          have hbc : br c ∈ branches := hbr_mem c hc_mem
          rw [hbr, List.mem_cons] at hbc
          rcases hbc with hbc | hbc
          · exact coversFinset_joinTrees (Or.inl (by
              rw [← hbc]; exact (hih c hc).2.2.2.2 j hjc))
          · exact coversFinset_joinTrees (Or.inr ⟨br c, hbc, (hih c hc).2.2.2.2 j hjc⟩)
      rw [toNiceSubtreeCore_eq_joinTrees toList R i hcs (by simpa only [br] using hbr)]
      exact ⟨hres_bag, hres_sv, hres_loc, hres_max, hres_cov⟩
termination_by n - i.val

open scoped Classical in
/-- Number of nodes in the subtree rooted at `i`. -/
private noncomputable def subtreeNodes {n : ℕ} (R : G.RootedTreeDecomposition n)
    (i : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter (R.IsDescendant · i)).card

omit [DecidableEq V] in
open scoped Classical in
private theorem subtreeNodes_zero {n : ℕ} (R : G.RootedTreeDecomposition n) :
    subtreeNodes R 0 = n + 1 := by
  have : Finset.univ.filter (R.IsDescendant · (0 : Fin (n + 1))) = Finset.univ := by
    ext j
    simp [R.isDescendant_zero j]
  rw [subtreeNodes, this, Finset.card_univ, Fintype.card_fin]

omit [DecidableEq V] in
open scoped Classical in
private theorem subtreeNodes_eq {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    subtreeNodes R i = 1 + ∑ c ∈ R.children i, subtreeNodes R c := by
  have hpart : Finset.univ.filter (R.IsDescendant · i) =
      insert i ((R.children i).biUnion fun c => Finset.univ.filter (R.IsDescendant · c)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (exists_mem_children_of_isDescendant hj hji)
    · rintro (hji | ⟨c, hc, hjc⟩)
      · subst hji; exact R.isDescendant_refl _
      · exact hjc.trans (R.isDescendant_of_mem_children hc)
  have hnot : i ∉ (R.children i).biUnion fun c => Finset.univ.filter (R.IsDescendant · c) := by
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and]
    intro c hc hci
    have h1 := R.lt_of_mem_children hc
    have h2 := hci.le
    exact absurd h1 (not_lt.2 h2)
  have hdisj : Set.PairwiseDisjoint (R.children i : Set (Fin (n + 1)))
      fun c => Finset.univ.filter (R.IsDescendant · c) := by
    intro c₁ hc₁ c₂ hc₂ hne s h1 h2 j hj
    have hj1 : j ∈ Finset.univ.filter (R.IsDescendant · c₁) := h1 hj
    have hj2 : j ∈ Finset.univ.filter (R.IsDescendant · c₂) := h2 hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    exact absurd (R.eq_of_mem_children hc₁ hc₂ hj1 hj2) hne
  rw [subtreeNodes, hpart, Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj,
    Nat.add_comm]
  rfl

private theorem size_toNiceSubtreeCore_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    (toNiceSubtreeCore toList R i).size + (2 * R.width + 3) ≤
      (3 * R.width + 5) * subtreeNodes R i := by
  by_cases hcs : (R.children i).sort (· ≤ ·) = []
  · rw [toNiceSubtreeCore, dite_eq_left hcs]
    have hno : ∀ c, c ∉ R.children i := fun c hc => by
      have : c ∈ (R.children i).sort (· ≤ ·) := (Finset.mem_sort _).2 hc
      rw [hcs] at this
      exact absurd this List.not_mem_nil
    have hempty : R.children i = ∅ := Finset.eq_empty_of_forall_notMem hno
    have hsn : subtreeNodes R i = 1 := by
      rw [subtreeNodes_eq, hempty, Finset.sum_empty, Nat.add_zero]
    rw [size_introduceChain, hsn, Nat.mul_one]
    have hlen := (length_le_card_of_listSpec hs (R.bag i)).trans (R.card_bag_le i)
    simp only [size_leaf]
    omega
  · set cs := (R.children i).sort (· ≤ ·)
    let br : Fin (n + 1) → NiceTree V := fun c =>
      niceStep toList R i c (toNiceSubtreeCore toList R c)
    have hbr_sz : ∀ c, c ∈ R.children i →
        (br c).size + 1 ≤ (3 * R.width + 5) * subtreeNodes R c := by
      intro c hc
      have _hlt : n - c.val < n - i.val := by
        have := R.lt_of_mem_children hc
        rw [Fin.lt_def] at this
        have hc_le : c.val ≤ n := Nat.lt_succ_iff.1 c.isLt
        omega
      have ih := size_toNiceSubtreeCore_le toList hs R c
      have h1 := (length_le_card_of_listSpec hs (R.bag i \ R.bag c)).trans
        ((Finset.card_le_card Finset.sdiff_subset).trans (R.card_bag_le i))
      have h2 := (length_le_card_of_listSpec hs (R.bag c \ R.bag i)).trans
        ((Finset.card_le_card Finset.sdiff_subset).trans (R.card_bag_le c))
      dsimp [br, niceStep]
      rw [size_introduceChain, size_forgetChain]
      omega
    let branches := cs.pmap (fun c _ => br c) (fun _ hc => hc)
    have hsum_list : ∀ (l : List (Fin (n + 1))) (hl : ∀ c ∈ l, c ∈ cs) (hnd : l.Nodup),
        ((l.pmap (fun c _ => br c) hl).map size).sum + l.length ≤
          (3 * R.width + 5) * ∑ c ∈ l.toFinset, subtreeNodes R c := by
      intro l
      induction l with
      | nil => simp
      | cons c l ih =>
        intro hl hnd
        rw [List.nodup_cons] at hnd
        have hmem_c : c ∈ R.children i := (Finset.mem_sort _).1 (hl c List.mem_cons_self)
        have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hnd.2
        have hc_not : c ∉ l.toFinset := by simpa [List.mem_toFinset] using hnd.1
        simp only [List.pmap_cons, List.map_cons, List.sum_cons, List.length_cons,
          List.toFinset_cons, Finset.sum_insert hc_not, Nat.mul_add]
        have hcsz := hbr_sz c hmem_c
        omega
    have hsum_br : (branches.map size).sum + branches.length ≤
        (3 * R.width + 5) * ∑ c ∈ R.children i, subtreeNodes R c := by
      have hlen : branches.length = cs.length := List.length_pmap
      have hto : cs.toFinset = R.children i := by
        ext c; simp [cs]
      have h := hsum_list cs (fun _ hc => hc) ((R.children i).sort_nodup _)
      change ((branches.map size).sum + cs.length) ≤ _ at h
      rwa [hto, ← hlen] at h
    cases hbr : branches with
    | nil =>
      have : cs.length = 0 := by
        have := congrArg List.length hbr
        simpa [branches] using this
      exact absurd (List.eq_nil_of_length_eq_zero this) hcs
    | cons b bs =>
      have hj : (joinTrees b bs).size + 1 = (branches.map size).sum + branches.length := by
        rw [size_joinTrees]
        have hlen : branches.length = 1 + bs.length := by rw [hbr, List.length_cons]; omega
        have hm : (branches.map size).sum = b.size + (bs.map size).sum := by rw [hbr]; simp
        omega
      have hsn := subtreeNodes_eq R i
      have hne_cs : (R.children i).Nonempty := by
        cases hcs_eq : cs with
        | nil => exact absurd hcs_eq hcs
        | cons c₀ _ =>
          have hc₀cs : c₀ ∈ cs := by rw [hcs_eq]; exact List.mem_cons_self
          exact ⟨c₀, (Finset.mem_sort _).1 hc₀cs⟩
      have hsum_pos : 0 < ∑ c ∈ R.children i, subtreeNodes R c := by
        obtain ⟨c₀, hc₀⟩ := hne_cs
        refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc₀)
        rw [subtreeNodes_eq]; omega
      rw [toNiceSubtreeCore_eq_joinTrees toList R i hcs hbr]
      have hmul : (3 * R.width + 5) * subtreeNodes R i =
          (3 * R.width + 5) + (3 * R.width + 5) * ∑ c ∈ R.children i, subtreeNodes R c := by
        rw [hsn, Nat.mul_add, Nat.mul_one]
      omega
termination_by n - i.val

private def toNiceDecompositionCore (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) : G.NiceTreeDecomposition where
  tree := toNiceCore toList R
  localValid := by
    obtain ⟨hbag, _, hloc, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    exact localValid_forgetChain (hs.nodup _) (fun v hv => by
      rw [hbag]; exact (hs.mem _ v).1 hv) hloc
  bag_root := by
    obtain ⟨hbag, _, _, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    rw [toNiceCore, bag_forgetChain, hbag, toFinset_of_listSpec hs, Finset.sdiff_self]
  exists_mem_bag v := by
    obtain ⟨_, hsv, _, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    rw [toNiceCore, subtreeVerts_forgetChain, hsv]
    exact R.mem_subtreeVerts_zero v
  exists_adj_mem_bag u v huv := by
    obtain ⟨i, hu, hv⟩ := R.exists_adj_mem_bag huv
    obtain ⟨_, _, _, _, hcov⟩ := toNiceSubtreeCore_props toList hs R 0
    refine coversFinset_forgetChain (coversFinset_mono ?_ (hcov i (R.isDescendant_zero i)))
    exact Finset.insert_subset hu (Finset.singleton_subset_iff.2 hv)

private theorem toNiceDecompositionCore_width_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (toNiceDecompositionCore toList hs R).width ≤ R.width := by
  obtain ⟨_, _, _, hmax, _⟩ := toNiceSubtreeCore_props toList hs R 0
  have hle : (toNiceCore toList R).maxBagCard ≤ R.width + 1 :=
    (maxBagCard_forgetChain_le _ _).trans hmax
  exact (NiceTreeDecomposition.width_le_iff _).2 hle

private theorem toNiceDecompositionCore_size_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (toNiceDecompositionCore toList hs R).size ≤ (3 * R.width + 5) * (n + 1) := by
  have hsub := size_toNiceSubtreeCore_le toList hs R 0
  rw [subtreeNodes_zero] at hsub
  have hlen := (length_le_card_of_listSpec hs (R.bag 0)).trans (R.card_bag_le 0)
  change (toNiceCore toList R).size ≤ _
  rw [toNiceCore, size_forgetChain]
  omega

/-- Convert a rooted tree decomposition into a nice tree decomposition using sorted bag lists
(computable when `[LinearOrder V]`), without increasing width. -/
def toNiceTree [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  toNiceDecompositionCore (fun S => S.sort (· ≤ ·))
    ⟨fun S => S.sort_nodup _, fun _ _ => Finset.mem_sort _⟩ R

theorem toNiceTree_width_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTree.width ≤ R.width :=
  toNiceDecompositionCore_width_le _ _ R

theorem toNiceTree_size_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTree.size ≤ (3 * R.width + 5) * (n + 1) :=
  toNiceDecompositionCore_size_le _ _ R

/-- Prune and convert a rooted tree decomposition into a nice tree decomposition with at most
`(3 * R.width + 5) * (card V + 1)` nodes and width at most `R.width`. -/
def toNiceTreePruned [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  R.prune.2.toNiceTree

theorem toNiceTreePruned_width_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTreePruned.width ≤ R.width :=
  R.prune.2.toNiceTree_width_le.trans R.prune_width_le

theorem toNiceTreePruned_size_le [LinearOrder V] [Fintype V] {n : ℕ}
    (R : G.RootedTreeDecomposition n) :
    R.toNiceTreePruned.size ≤ (3 * R.width + 5) * (Fintype.card V + 1) := by
  refine R.prune.2.toNiceTree_size_le.trans ?_
  have hw : R.prune.2.width ≤ R.width := R.prune_width_le
  have hn : R.prune.1 ≤ Fintype.card V := R.prune_nodes_le
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Convert any rooted tree decomposition into a nice tree decomposition without requiring a
linear order on `V`. -/
noncomputable def toNice {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  toNiceDecompositionCore Finset.toList
    ⟨fun S => S.nodup_toList, fun _ _ => Finset.mem_toList⟩ R

theorem toNice_width_le {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNice.width ≤ R.width :=
  toNiceDecompositionCore_width_le _ _ R

theorem toNice_size_le [Fintype V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (R.prune.2.toNice).size ≤ (3 * R.width + 5) * (Fintype.card V + 1) := by
  refine (toNiceDecompositionCore_size_le _ _ R.prune.2).trans ?_
  have hw : R.prune.2.width ≤ R.width := R.prune_width_le
  have hn : R.prune.1 ≤ Fintype.card V := R.prune_nodes_le
  exact Nat.mul_le_mul (by omega) (by omega)

end RootedTreeDecomposition

namespace TreeDecomposition

variable {V : Type uV} {ι : Type uι} {G : SimpleGraph V} [DecidableEq V]

/-- Every finite tree decomposition has a nice tree decomposition of width at most `D.width` and
at most `(3 * D.width + 5) * (card V + 1)` nodes (when `V` is finite). -/
theorem exists_niceTreeDecomposition [Fintype ι] [Fintype V] (D : G.TreeDecomposition ι) :
    ∃ N : G.NiceTreeDecomposition,
      N.width ≤ D.width ∧ N.size ≤ (3 * D.width + 5) * (Fintype.card V + 1) := by
  obtain ⟨_, R, hR⟩ := D.exists_rooted_width_eq
  refine ⟨R.prune.2.toNice, ?_, ?_⟩
  · exact (R.prune.2.toNice_width_le).trans (R.prune_width_le.trans hR.le)
  · simpa [hR] using R.toNice_size_le

end TreeDecomposition

end SimpleGraph
