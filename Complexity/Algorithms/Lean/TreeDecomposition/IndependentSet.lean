/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Subtree
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Tactic.Linarith

/-!
# Maximum-weight independent set over a tree decomposition

Given a graph `G` with a rooted tree decomposition `R : G.RootedTreeDecomposition n` and vertex
weights `w : V → ℕ`, the dynamic program `mwisValue R w` is the maximum total weight of an
independent set of `G`. The charged version `mwisM R w` returns the same value. If `R` has width at
most `k`, its declared cost is at most `(n + 1) · 2 ^ (k + 1) · (2 (k + 1) ^ 2 + 2 (k + 1) + 6)`
ticks, where `n + 1` is the number of decomposition nodes, not the number of vertices. These ticks
are a declared per-node cost function, not a count of the operations the Lean program performs;
see "Cost model and limitations" below. The executable program `mwisFPT` of
`Complexity.Algorithms.Lean.TreeDecomposition.IndependentSetFPT` materializes the tables, charges
its ticks inside the loops that do the work, and has the bound `time_mwisFPT_le`.

The program processes the nodes in decreasing order, so every child is handled before its
parent. Node `i` keeps a table indexed by the subsets `S` of its bag. Once all children of `i`
are processed, the entry for an independent `S` is the largest weight of a set `J` of vertices
below `i` and outside the bag of `i` such that `J ∪ S` is independent. Processing a child `j`
with parent `p` adds to the table of `p`, at `S`, the best value over the subsets `T` of the bag
of `j` that are independent and agree with `S` on the shared vertices. The answer is the best
value over the independent subsets of the root bag. Because every child table is indexed by its
intersection with the parent bag, the program works on arbitrary rooted decompositions: it needs
no nice decomposition and no separate join nodes.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.mwisValue`: the value computed by the program.
* `Cslib.Algorithms.Lean.TreeDecomposition.mwisM`: the same value in `TimeM ℕ`, with the declared
  per-node cost.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.isGreatest_mwisValue`: `mwisValue R w` is the maximum
  of `∑ v ∈ I, w v` over the independent finite sets `I`.
* `Cslib.Algorithms.Lean.TreeDecomposition.mwisValue_one_eq_indepNum`: with unit weights it is
  the independence number.
* `Cslib.Algorithms.Lean.TreeDecomposition.time_mwisM_le`: if `R` has width at most `k`, the
  declared cost is at most `(n + 1) · 2 ^ (k + 1) · (2 (k + 1) ^ 2 + 2 (k + 1) + 6)` ticks.

## Cost model and limitations

The ticks of `mwisM` are a declared cost function: `tablesM` charges one lump tick
`stepCost (#bag j) (#bag (parent j))` per nonroot node `j` and `mwisM` charges `rootCost (#bag 0)`
at the root. They describe an implementation that is not formalized here. That implementation
stores each bag as an array of at most `k + 1` vertices, represents subsets of a bag as bit masks,
stores each table as an array indexed by masks, and answers adjacency queries `G.Adj u v` and
weight lookups `w v` in unit time (a unit-cost RAM with an adjacency matrix). Additions and
comparisons of weights cost one unit. Processing a child with bag size `b` and parent bag size
`q` is charged `stepCost b q`:

* `b * q` to locate the bag vertices of the child in the parent bag;
* for each of the `2 ^ b` subsets `T` of the child bag: `b * b` adjacency tests for independence,
  `b` membership and weight operations to project `T` onto the parent bag and sum the weight of
  the forgotten vertices, and `4` for the table lookup, comparison, update and zero
  initialization of the child-side table;
* for each of the `2 ^ q` subsets `S` of the parent bag: `q` operations to project `S` onto the
  child bag and `2` for the lookup and addition.

The root is charged `rootCost r = 2 ^ r * (r * r + r + 3)` for root bag size `r`. A node's own
table is zero-initialized once, at `2 ^ (#bag)` unit steps; this is charged as the zero
initialization in the node's own `stepCost` (or in `rootCost` at the root), so it changes only the
constant. Reading the input and building the bag arrays are not charged.

The value is computed by the specification-level functions `forget`, `step` and `tables`. They
are not that array implementation, and it is not proved that the array implementation computes
the same values or performs the charged number of operations. In particular, the tables are
closures and are never materialized, so `forget` re-evaluates the child closures, and evaluating
`mwisM` or `mwisValue` as written takes time exponential in the depth of the decomposition. It is
not an FPT computation. The executable program whose ticks track the operations it performs is
`mwisFPT` in `Complexity.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`: its value is
`mwisValue` (`ret_mwisFPT`) and its tick bound is `time_mwisFPT_le`.

The node count `n + 1` is a parameter of the decomposition and is not bounded in terms of
`card V` here. The decomposition is supplied by the caller; computing one is a separate problem.
The specification and the correctness theorems are universe polymorphic. The charged part takes
`V : Type`, because the tables `Fin (n + 1) → Finset V → ℕ` must live in the universe of the
`TimeM` monad's values, and `TimeM ℕ` is a monad on `Type`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.3.1][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open SimpleGraph SimpleGraph.RootedTreeDecomposition

/-! ### The dynamic program -/

section Program

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

variable (G) in
/-- The message from a child with bag `B` and table `f` to its parent with bag `P`, at a subset
`S` of `P`: the best value of `(∑ v ∈ T \ P, w v) + f T` over the independent subsets `T ⊆ B`
that agree with `S` on `B ∩ P`. -/
@[expose] def forget (w : V → ℕ) (B P : Finset V) (f : Finset V → ℕ) (S : Finset V) : ℕ :=
  (B.powerset.filter fun T : Finset V => G.IsIndepSet (↑T : Set V) ∧ T ∩ P = S ∩ B).sup
    fun T => (∑ v ∈ T \ P, w v) + f T

/-- Process node `j`: add its message to the table of its parent. -/
@[expose] def step (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (acc : Fin (n + 1) → Finset V → ℕ) (j : Fin (n + 1)) : Fin (n + 1) → Finset V → ℕ :=
  Function.update acc (R.parent j) fun S =>
    acc (R.parent j) S + forget G w (R.bag j) (R.bag (R.parent j)) (acc j) S

/-- The tables after processing the nodes `n, n - 1, …, n - t + 1`. -/
@[expose] def tables (R : G.RootedTreeDecomposition n) (w : V → ℕ) :
    ℕ → Fin (n + 1) → Finset V → ℕ
  | 0 => fun _ _ => 0
  | t + 1 => step R w (tables R w t) (Fin.ofNat (n + 1) (n - t))

/-- The value of the dynamic program: the best value of `(∑ v ∈ S, w v) + table S` over the
independent subsets `S` of the root bag, after processing every nonroot node. -/
@[expose] def mwisValue (R : G.RootedTreeDecomposition n) (w : V → ℕ) : ℕ :=
  ((R.bag 0).powerset.filter fun S : Finset V => G.IsIndepSet (↑S : Set V)).sup fun S =>
    (∑ v ∈ S, w v) + tables R w n 0 S

end Program

/-! ### Correctness -/

section Correctness

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private theorem isIndepSet_iff_forall {S : Finset V} :
    G.IsIndepSet (↑S : Set V) ↔ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y :=
  ⟨fun h _ hx _ hy hxy => h hx hy hxy.ne hxy, fun h _ hx _ hy _ => h _ hx _ hy⟩

private theorem isIndepSet_of_subset {S T : Finset V} (hT : G.IsIndepSet (↑T : Set V))
    (h : S ⊆ T) : G.IsIndepSet (↑S : Set V) :=
  Set.Pairwise.mono (Finset.coe_subset.2 h) hT

variable [DecidableEq V] [DecidableRel G.Adj] (R : G.RootedTreeDecomposition n) (w : V → ℕ)

/-- The vertices below `i` and outside its bag. -/
private noncomputable def below (i : Fin (n + 1)) : Finset V :=
  R.subtreeVerts i \ R.bag i

/-- The intended table of node `i` at `S`. -/
private noncomputable def opt (i : Fin (n + 1)) (S : Finset V) : ℕ :=
  ((below R i).powerset.filter fun J : Finset V => G.IsIndepSet (↑(J ∪ S) : Set V)).sup
    fun J => ∑ v ∈ J, w v

/-- The intended message from `c` to its parent at `S`. -/
private noncomputable def msg (c : Fin (n + 1)) (S : Finset V) : ℕ :=
  ((R.subtreeVerts c \ R.bag (R.parent c)).powerset.filter
    fun J : Finset V => G.IsIndepSet (↑(J ∪ S) : Set V)).sup
      fun J => ∑ v ∈ J, w v

variable {R w}

private theorem sum_le_opt {i : Fin (n + 1)} {S J : Finset V} (hJ : J ⊆ below R i)
    (hJS : G.IsIndepSet (↑(J ∪ S) : Set V)) : ∑ v ∈ J, w v ≤ opt R w i S :=
  Finset.le_sup (f := fun J => ∑ v ∈ J, w v) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJ, hJS⟩)

private theorem exists_opt (i : Fin (n + 1)) {S : Finset V} (hS : G.IsIndepSet (↑S : Set V)) :
    ∃ J ⊆ below R i, G.IsIndepSet (↑(J ∪ S) : Set V) ∧ opt R w i S = ∑ v ∈ J, w v := by
  have h0 : (∅ : Finset V) ∈ (below R i).powerset.filter
      fun J : Finset V => G.IsIndepSet (↑(J ∪ S) : Set V) :=
    Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by rwa [Finset.empty_union]⟩
  obtain ⟨J, hJ, hJeq⟩ := Finset.exists_mem_eq_sup _ ⟨∅, h0⟩ fun J => ∑ v ∈ J, w v
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  exact ⟨J, hJ.1, hJ.2, hJeq⟩

private theorem sum_le_msg {c : Fin (n + 1)} {S J : Finset V}
    (hJ : J ⊆ R.subtreeVerts c \ R.bag (R.parent c)) (hJS : G.IsIndepSet (↑(J ∪ S) : Set V)) :
    ∑ v ∈ J, w v ≤ msg R w c S :=
  Finset.le_sup (f := fun J => ∑ v ∈ J, w v) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJ, hJS⟩)

private theorem exists_msg (c : Fin (n + 1)) {S : Finset V} (hS : G.IsIndepSet (↑S : Set V)) :
    ∃ J ⊆ R.subtreeVerts c \ R.bag (R.parent c), G.IsIndepSet (↑(J ∪ S) : Set V) ∧
      msg R w c S = ∑ v ∈ J, w v := by
  have h0 : (∅ : Finset V) ∈ (R.subtreeVerts c \ R.bag (R.parent c)).powerset.filter
      fun J : Finset V => G.IsIndepSet (↑(J ∪ S) : Set V) :=
    Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by rwa [Finset.empty_union]⟩
  obtain ⟨J, hJ, hJeq⟩ := Finset.exists_mem_eq_sup _ ⟨∅, h0⟩ fun J => ∑ v ∈ J, w v
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  exact ⟨J, hJ.1, hJ.2, hJeq⟩

private theorem forget_congr {B P : Finset V} {f g : Finset V → ℕ}
    (h : ∀ T ⊆ B, G.IsIndepSet (↑T : Set V) → f T = g T) (S : Finset V) :
    forget G w B P f S = forget G w B P g S := by
  unfold forget
  refine Finset.sup_congr rfl fun T hT => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  rw [h T hT.1 hT.2.1]

/-- The message computed from the intended table of a child is the intended message. -/
private theorem forget_opt {c : Fin (n + 1)} {S : Finset V}
    (hSP : S ⊆ R.bag (R.parent c)) (hS : G.IsIndepSet (↑S : Set V)) :
    forget G w (R.bag c) (R.bag (R.parent c)) (opt R w c) S = msg R w c S := by
  refine le_antisymm (Finset.sup_le fun T hT => ?_) (Finset.sup_le fun K hK => ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTB, hTi, hTP⟩ := hT
    obtain ⟨J, hJ, hJi, hJeq⟩ := exists_opt (w := w) c hTi
    -- `K = (T \ P) ∪ J` lies below `c`, outside `P`, and inside `J ∪ T`.
    have hK : ∀ x ∈ (T \ R.bag (R.parent c)) ∪ J,
        x ∈ R.subtreeVerts c ∧ x ∉ R.bag (R.parent c) ∧ x ∈ J ∪ T := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨hxT, hxP⟩ := Finset.mem_sdiff.1 hx
        exact ⟨R.bag_subset_subtreeVerts c (hTB hxT), hxP, Finset.mem_union_right _ hxT⟩
      · obtain ⟨hxs, hxB⟩ := Finset.mem_sdiff.1 (hJ hx)
        exact ⟨hxs, fun hxP => hxB (mem_bag_of_mem_subtreeVerts_of_mem_bag_parent hxs hxP),
          Finset.mem_union_left _ hx⟩
    have hcross : ∀ x ∈ (T \ R.bag (R.parent c)) ∪ J, ∀ y ∈ S, ¬G.Adj x y := by
      intro x hx y hy hxy
      obtain ⟨hxs, hxP, hxJT⟩ := hK x hx
      have hys := mem_subtreeVerts_of_adj hxs hxP hxy
      have hyB := mem_bag_of_mem_subtreeVerts_of_mem_bag_parent hys (hSP hy)
      have hyT : y ∈ T := by
        have : y ∈ S ∩ R.bag c := Finset.mem_inter.2 ⟨hy, hyB⟩
        rw [← hTP] at this
        exact (Finset.mem_inter.1 this).1
      exact isIndepSet_iff_forall.1 hJi x hxJT y (Finset.mem_union_right _ hyT) hxy
    have hKS : G.IsIndepSet (↑((T \ R.bag (R.parent c)) ∪ J ∪ S) : Set V) := by
      refine isIndepSet_iff_forall.2 fun x hx y hy hxy => ?_
      rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
      · exact isIndepSet_iff_forall.1 hJi x (hK x hx).2.2 y (hK y hy).2.2 hxy
      · exact hcross x hx y hy hxy
      · exact hcross y hy x hx hxy.symm
      · exact isIndepSet_iff_forall.1 hS x hx y hy hxy
    have hKsub : (T \ R.bag (R.parent c)) ∪ J ⊆ R.subtreeVerts c \ R.bag (R.parent c) :=
      fun x hx => Finset.mem_sdiff.2 ⟨(hK x hx).1, (hK x hx).2.1⟩
    have hdisj : Disjoint (T \ R.bag (R.parent c)) J := by
      refine Finset.disjoint_left.2 fun x hx hxJ => ?_
      exact (Finset.mem_sdiff.1 (hJ hxJ)).2 (hTB (Finset.mem_sdiff.1 hx).1)
    calc (∑ v ∈ T \ R.bag (R.parent c), w v) + opt R w c T
        = ∑ v ∈ (T \ R.bag (R.parent c)) ∪ J, w v := by rw [hJeq, Finset.sum_union hdisj]
      _ ≤ msg R w c S := sum_le_msg hKsub hKS
  · rw [Finset.mem_filter, Finset.mem_powerset] at hK
    obtain ⟨hKsub, hKS⟩ := hK
    have hKP : ∀ x ∈ K, x ∉ R.bag (R.parent c) := fun x hx => (Finset.mem_sdiff.1 (hKsub hx)).2
    have hKs : ∀ x ∈ K, x ∈ R.subtreeVerts c := fun x hx => (Finset.mem_sdiff.1 (hKsub hx)).1
    have hTB : K ∩ R.bag c ∪ S ∩ R.bag c ⊆ R.bag c :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hTKS : K ∩ R.bag c ∪ S ∩ R.bag c ⊆ K ∪ S :=
      Finset.union_subset_union Finset.inter_subset_left Finset.inter_subset_left
    have hTP : (K ∩ R.bag c ∪ S ∩ R.bag c) ∩ R.bag (R.parent c) = S ∩ R.bag c := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨⟨hxK, -⟩ | h, hxP⟩
        · exact absurd hxP (hKP x hxK)
        · exact h
      · intro h
        exact ⟨.inr h, hSP h.1⟩
    have hJsub : K \ R.bag c ⊆ below R c := by
      intro x hx
      obtain ⟨hxK, hxB⟩ := Finset.mem_sdiff.1 hx
      exact Finset.mem_sdiff.2 ⟨hKs x hxK, hxB⟩
    have hJT : K \ R.bag c ∪ (K ∩ R.bag c ∪ S ∩ R.bag c) ⊆ K ∪ S :=
      Finset.union_subset (Finset.sdiff_subset.trans Finset.subset_union_left) hTKS
    have hTsdiff : (K ∩ R.bag c ∪ S ∩ R.bag c) \ R.bag (R.parent c) = K ∩ R.bag c := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hxP⟩
        · exact h
        · exact absurd (hSP h.1) hxP
      · intro h
        exact ⟨.inl h, hKP x h.1⟩
    have hle := sum_le_opt (w := w) hJsub (isIndepSet_of_subset hKS hJT)
    have hmem : K ∩ R.bag c ∪ S ∩ R.bag c ∈ (R.bag c).powerset.filter fun T : Finset V =>
        G.IsIndepSet (↑T : Set V) ∧ T ∩ R.bag (R.parent c) = S ∩ R.bag c :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hTB, isIndepSet_of_subset hKS hTKS, hTP⟩
    calc ∑ v ∈ K, w v = (∑ v ∈ K ∩ R.bag c, w v) + ∑ v ∈ K \ R.bag c, w v :=
          (Finset.sum_inter_add_sum_sdiff K (R.bag c) w).symm
      _ ≤ (∑ v ∈ (K ∩ R.bag c ∪ S ∩ R.bag c) \ R.bag (R.parent c), w v) +
            opt R w c (K ∩ R.bag c ∪ S ∩ R.bag c) := by
          rw [hTsdiff]
          exact Nat.add_le_add_left hle _
      _ ≤ forget G w (R.bag c) (R.bag (R.parent c)) (opt R w c) S :=
          Finset.le_sup (f := fun T => (∑ v ∈ T \ R.bag (R.parent c), w v) + opt R w c T)
            hmem

/-- The intended table of a node is the sum of the intended messages of its children. -/
private theorem opt_eq_sum {i : Fin (n + 1)} {S : Finset V} (hS : G.IsIndepSet (↑S : Set V)) :
    opt R w i S = ∑ c ∈ R.children i, msg R w c S := by
  have hpar : ∀ c ∈ R.children i, R.parent c = i := fun c hc => (mem_children.1 hc).2
  refine le_antisymm (Finset.sup_le fun J hJ => ?_) ?_
  · rw [Finset.mem_filter, Finset.mem_powerset] at hJ
    obtain ⟨hJsub, hJS⟩ := hJ
    have hcover : J = (R.children i).biUnion fun c => J ∩ R.subtreeVerts c := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · intro hx
        obtain ⟨hxs, hxi⟩ := Finset.mem_sdiff.1 (hJsub hx)
        obtain ⟨c, hc, hxc⟩ := exists_mem_children_of_mem_subtreeVerts hxs hxi
        exact ⟨c, hc, hx, hxc⟩
      · rintro ⟨c, -, hx, -⟩
        exact hx
    have hdisj : (↑(R.children i) : Set (Fin (n + 1))).PairwiseDisjoint
        fun c => J ∩ R.subtreeVerts c := by
      intro c hc c' hc' hne
      refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
      obtain ⟨hxJ, hxc⟩ := Finset.mem_inter.1 hx
      exact eq_of_mem_subtreeVerts_of_mem_children hc hc' hxc (Finset.mem_inter.1 hx').2
        (Finset.mem_sdiff.1 (hJsub hxJ)).2
    have hle : ∀ c ∈ R.children i, ∑ v ∈ J ∩ R.subtreeVerts c, w v ≤ msg R w c S := by
      intro c hc
      refine sum_le_msg (fun x hx => ?_)
        (isIndepSet_of_subset hJS (Finset.union_subset_union Finset.inter_subset_left le_rfl))
      obtain ⟨hxJ, hxc⟩ := Finset.mem_inter.1 hx
      rw [hpar c hc]
      exact Finset.mem_sdiff.2 ⟨hxc, (Finset.mem_sdiff.1 (hJsub hxJ)).2⟩
    calc ∑ v ∈ J, w v = ∑ c ∈ R.children i, ∑ v ∈ J ∩ R.subtreeVerts c, w v := by
          conv_lhs => rw [hcover]
          exact Finset.sum_biUnion hdisj
      _ ≤ ∑ c ∈ R.children i, msg R w c S := Finset.sum_le_sum hle
  · choose K hKsub hKS hKeq using fun c => exists_msg (R := R) (w := w) c hS
    have hdisj : (↑(R.children i) : Set (Fin (n + 1))).PairwiseDisjoint K := by
      intro c hc c' hc' hne
      refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
      obtain ⟨hxc, hxp⟩ := Finset.mem_sdiff.1 (hKsub c hx)
      obtain ⟨hxc', -⟩ := Finset.mem_sdiff.1 (hKsub c' hx')
      rw [hpar c hc] at hxp
      exact eq_of_mem_subtreeVerts_of_mem_children hc hc' hxc hxc' hxp
    set J := (R.children i).biUnion K with hJdef
    have hmemJ : ∀ x ∈ J, ∃ c ∈ R.children i, x ∈ K c := fun x hx => Finset.mem_biUnion.1 hx
    have hJsub : J ⊆ below R i := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hmemJ x hx
      obtain ⟨hxs, hxp⟩ := Finset.mem_sdiff.1 (hKsub c hxc)
      rw [hpar c hc] at hxp
      exact Finset.mem_sdiff.2 ⟨subtreeVerts_subset_of_mem_children hc hxs, hxp⟩
    have hJS : G.IsIndepSet (↑(J ∪ S) : Set V) := by
      -- A vertex of `K c` and a neighbour of it in `J ∪ S` lie in `K c ∪ S`.
      have hkey : ∀ c ∈ R.children i, ∀ x ∈ K c, ∀ y ∈ J ∪ S, G.Adj x y → y ∈ K c ∪ S := by
        intro c hc x hx y hy hxy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨c', hc', hyc'⟩ := hmemJ y hy
          obtain ⟨hxs, hxp⟩ := Finset.mem_sdiff.1 (hKsub c hx)
          have hys := mem_subtreeVerts_of_adj hxs hxp hxy
          obtain ⟨hys', hyp'⟩ := Finset.mem_sdiff.1 (hKsub c' hyc')
          rw [hpar c' hc'] at hyp'
          rw [eq_of_mem_subtreeVerts_of_mem_children hc hc' hys hys' hyp']
          exact Finset.mem_union_left _ hyc'
        · exact Finset.mem_union_right _ hy
      refine isIndepSet_iff_forall.2 fun x hx y hy hxy => ?_
      rcases Finset.mem_union.1 hx with hx' | hx'
      · obtain ⟨c, hc, hxc⟩ := hmemJ x hx'
        exact isIndepSet_iff_forall.1 (hKS c) x (Finset.mem_union_left _ hxc) y
          (hkey c hc x hxc y hy hxy) hxy
      · rcases Finset.mem_union.1 hy with hy' | hy'
        · obtain ⟨c, hc, hyc⟩ := hmemJ y hy'
          exact isIndepSet_iff_forall.1 (hKS c) y (Finset.mem_union_left _ hyc) x
            (hkey c hc y hyc x hx hxy.symm) hxy.symm
        · exact isIndepSet_iff_forall.1 hS x hx' y hy' hxy
    calc ∑ c ∈ R.children i, msg R w c S = ∑ c ∈ R.children i, ∑ v ∈ K c, w v :=
          Finset.sum_congr rfl fun c _ => hKeq c
      _ = ∑ v ∈ J, w v := (Finset.sum_biUnion hdisj).symm
      _ ≤ opt R w i S := sum_le_opt hJsub hJS

private theorem val_ofNat_sub {t : ℕ} (ht : t < n) :
    (Fin.ofNat (n + 1) (n - t)).val = n - t := by
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- After processing the nodes `n, …, n - t + 1`, the table of each node is the sum of the
intended messages of its processed children. -/
private theorem tables_eq_sum {t : ℕ} (ht : t ≤ n) {i : Fin (n + 1)} {S : Finset V}
    (hSi : S ⊆ R.bag i) (hS : G.IsIndepSet (↑S : Set V)) :
    tables R w t i S = ∑ c ∈ (R.children i).filter (fun c => n - t < c.val), msg R w c S := by
  induction t generalizing i S with
  | zero =>
    rw [Finset.filter_false_of_mem fun c _ => by have := c.isLt; omega, Finset.sum_empty]
    rfl
  | succ t ih =>
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j = Fin.ofNat (n + 1) (n - t) := ⟨_, rfl⟩
    have hjv : j.val = n - t := hj ▸ val_ofNat_sub (by omega)
    have hj0 : j ≠ 0 := fun h => by
      rw [h, Fin.val_zero] at hjv
      omega
    have hstep : tables R w (t + 1) = step R w (tables R w t) j := by
      rw [hj]
      rfl
    rw [hstep]
    unfold step
    by_cases hi : i = R.parent j
    · subst hi
      rw [Function.update_self]
      -- The table of `j` is complete: all its children are processed.
      have hjopt : ∀ T ⊆ R.bag j, G.IsIndepSet (↑T : Set V) →
          tables R w t j T = opt R w j T := by
        intro T hT hTi
        rw [ih (by omega) hT hTi, opt_eq_sum hTi]
        refine Finset.sum_congr (Finset.filter_true_of_mem fun c hc => ?_) fun _ _ => rfl
        have := lt_of_mem_children hc
        rw [Fin.lt_def] at this
        omega
      rw [forget_congr hjopt, forget_opt hSi hS, ih (by omega) hSi hS]
      have hjmem : j ∈ R.children (R.parent j) := mem_children.2 ⟨hj0, rfl⟩
      have hfilter : (R.children (R.parent j)).filter (fun c => n - (t + 1) < c.val) =
          insert j ((R.children (R.parent j)).filter (fun c => n - t < c.val)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hc, hlt⟩
          by_cases hcj : c = j
          · exact .inl hcj
          · refine .inr ⟨hc, ?_⟩
            have : c.val ≠ j.val := fun h => hcj (Fin.ext h)
            omega
        · rintro (rfl | ⟨hc, hlt⟩)
          · exact ⟨hjmem, by omega⟩
          · exact ⟨hc, by omega⟩
      have hjnot : j ∉ (R.children (R.parent j)).filter (fun c => n - t < c.val) := by
        rw [Finset.mem_filter]
        omega
      rw [hfilter, Finset.sum_insert hjnot, Nat.add_comm]
    · rw [Function.update_of_ne hi, ih (by omega) hSi hS]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp only [Finset.mem_filter]
      refine and_congr_right fun hc => ?_
      have hcj : c ≠ j := by
        rintro rfl
        exact hi (mem_children.1 hc).2.symm
      have : c.val ≠ j.val := fun h => hcj (Fin.ext h)
      omega

private theorem tables_eq_opt {i : Fin (n + 1)} {S : Finset V} (hSi : S ⊆ R.bag i)
    (hS : G.IsIndepSet (↑S : Set V)) : tables R w n i S = opt R w i S := by
  rw [tables_eq_sum le_rfl hSi hS, opt_eq_sum hS]
  refine Finset.sum_congr (Finset.filter_true_of_mem fun c hc => ?_) fun _ _ => rfl
  have := lt_of_mem_children hc
  rw [Fin.lt_def] at this
  omega

/-- **Correctness.** The value of the dynamic program is the maximum weight of an independent
set: it is attained by an independent set and bounds the weight of every independent set. -/
theorem isGreatest_mwisValue (R : G.RootedTreeDecomposition n) (w : V → ℕ) :
    IsGreatest {x | ∃ I : Finset V, G.IsIndepSet (↑I : Set V) ∧ ∑ v ∈ I, w v = x}
      (mwisValue R w) := by
  have hval : mwisValue R w =
      ((R.bag 0).powerset.filter fun S : Finset V => G.IsIndepSet (↑S : Set V)).sup
        fun S => (∑ v ∈ S, w v) + opt R w 0 S := by
    unfold mwisValue
    refine Finset.sup_congr rfl fun S hS => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [tables_eq_opt hS.1 hS.2]
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup
      ((R.bag 0).powerset.filter fun S : Finset V => G.IsIndepSet (↑S : Set V))
      ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by
        simp only [Finset.coe_empty, Set.pairwise_empty]⟩⟩
      fun S => (∑ v ∈ S, w v) + opt R w 0 S
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨J, hJ, hJS, hJeq⟩ := exists_opt (R := R) (w := w) 0 hS.2
    have hdisj : Disjoint J S := Finset.disjoint_left.2 fun x hxJ hxS =>
      (Finset.mem_sdiff.1 (hJ hxJ)).2 (hS.1 hxS)
    refine ⟨J ∪ S, hJS, ?_⟩
    rw [hval, hSeq, hJeq, Finset.sum_union hdisj, Nat.add_comm]
  · rintro x ⟨I, hI, rfl⟩
    have hsub : I ∩ R.bag 0 ⊆ R.bag 0 := Finset.inter_subset_right
    have hSi : G.IsIndepSet (↑(I ∩ R.bag 0) : Set V) :=
      isIndepSet_of_subset hI Finset.inter_subset_left
    have hJ : I \ R.bag 0 ⊆ below R 0 := fun x hx =>
      Finset.mem_sdiff.2 ⟨R.mem_subtreeVerts_zero x, (Finset.mem_sdiff.1 hx).2⟩
    have hJS : G.IsIndepSet (↑(I \ R.bag 0 ∪ I ∩ R.bag 0) : Set V) := by
      rwa [Finset.sdiff_union_inter]
    have hmem : I ∩ R.bag 0 ∈
        (R.bag 0).powerset.filter fun S : Finset V => G.IsIndepSet (↑S : Set V) :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hSi⟩
    calc ∑ v ∈ I, w v = (∑ v ∈ I ∩ R.bag 0, w v) + ∑ v ∈ I \ R.bag 0, w v :=
          (Finset.sum_inter_add_sum_sdiff I (R.bag 0) w).symm
      _ ≤ (∑ v ∈ I ∩ R.bag 0, w v) + opt R w 0 (I ∩ R.bag 0) :=
          Nat.add_le_add_left (sum_le_opt hJ hJS) _
      _ ≤ mwisValue R w := by
          rw [hval]
          exact Finset.le_sup (f := fun S => (∑ v ∈ S, w v) + opt R w 0 S) hmem

/-- With unit weights the dynamic program computes the independence number. -/
theorem mwisValue_one_eq_indepNum (R : G.RootedTreeDecomposition n) :
    mwisValue R (fun _ => 1) = G.indepNum := by
  have := R.toTreeDecomposition.finite
  obtain ⟨⟨I, hI, hIeq⟩, hub⟩ := isGreatest_mwisValue R (fun _ => 1)
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G)
  refine le_antisymm ?_ ?_
  · rw [← hIeq, Finset.sum_const, smul_eq_mul, mul_one]
    exact hI.card_le_indepNum
  · have := hub ⟨s, hs.isIndepSet, rfl⟩
    rwa [Finset.sum_const, smul_eq_mul, mul_one, hs.card_eq] at this

end Correctness


/-! ### Declared cost -/

/-- Ticks charged for processing a child with bag size `b` whose parent has bag size `q`, in the
declared cost model of the module docstring. -/
@[expose] def stepCost (b q : ℕ) : ℕ :=
  b * q + 2 ^ b * (b * b + b + 4) + 2 ^ q * (q + 2)

/-- Ticks charged at the root, with root bag size `r`, in the declared cost model. -/
@[expose] def rootCost (r : ℕ) : ℕ :=
  2 ^ r * (r * r + r + 3)

/-- The per-node bound `2 ^ m (2 m ^ 2 + 2 m + 6)` for bags of size at most `m`. -/
@[expose] def nodeCost (m : ℕ) : ℕ :=
  2 ^ m * (2 * m * m + 2 * m + 6)

theorem stepCost_mono {b b' q q' : ℕ} (hb : b ≤ b') (hq : q ≤ q') :
    stepCost b q ≤ stepCost b' q' := by
  unfold stepCost
  have h1 : 2 ^ b ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hb
  have h2 : 2 ^ q ≤ 2 ^ q' := Nat.pow_le_pow_right (by norm_num) hq
  gcongr

theorem rootCost_mono {r r' : ℕ} (hr : r ≤ r') : rootCost r ≤ rootCost r' := by
  unfold rootCost
  have h1 : 2 ^ r ≤ 2 ^ r' := Nat.pow_le_pow_right (by norm_num) hr
  gcongr

theorem stepCost_le_nodeCost (m : ℕ) : stepCost m m ≤ nodeCost m := by
  unfold stepCost nodeCost
  have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : m * m ≤ 2 ^ m * (m * m) := Nat.le_mul_of_pos_left _ h
  nlinarith

theorem rootCost_le_nodeCost (m : ℕ) : rootCost m ≤ nodeCost m := by
  unfold rootCost nodeCost
  gcongr <;> omega

section Charged

variable {V : Type} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

/-- `tables` in `TimeM ℕ`, charging the declared lump cost `stepCost` per processed node. The
tick is not a count of the operations performed by `step`. For the executable table pass whose
ticks are charged inside its loops, see `tablesFPT` in
`Complexity.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`. -/
@[expose] def tablesM (R : G.RootedTreeDecomposition n) (w : V → ℕ) :
    ℕ → TimeM ℕ (Fin (n + 1) → Finset V → ℕ)
  | 0 => pure fun _ _ => 0
  | t + 1 => do
    let acc ← tablesM R w t
    let j : Fin (n + 1) := Fin.ofNat (n + 1) (n - t)
    TimeM.tick (stepCost (R.bag j).card (R.bag (R.parent j)).card)
    pure (step R w acc j)

/-- The dynamic program in `TimeM ℕ`, with the declared per-node cost of the module docstring.
The executable program with materialized tables is `mwisFPT` in
`Complexity.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`. -/
@[expose] def mwisM (R : G.RootedTreeDecomposition n) (w : V → ℕ) : TimeM ℕ ℕ := do
  let acc ← tablesM R w n
  TimeM.tick (rootCost (R.bag 0).card)
  pure (((R.bag 0).powerset.filter fun S : Finset V => G.IsIndepSet (↑S : Set V)).sup fun S =>
    (∑ v ∈ S, w v) + acc 0 S)

@[simp] theorem ret_tablesM (R : G.RootedTreeDecomposition n) (w : V → ℕ) (t : ℕ) :
    (tablesM R w t).ret = tables R w t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [tablesM, tables, TimeM.ret_bind, TimeM.ret_pure, ih]

@[simp] theorem ret_mwisM (R : G.RootedTreeDecomposition n) (w : V → ℕ) :
    (mwisM R w).ret = mwisValue R w := by
  simp only [mwisM, mwisValue, TimeM.ret_bind, TimeM.ret_pure, ret_tablesM]

theorem time_tablesM_le (R : G.RootedTreeDecomposition n) (w : V → ℕ) {k : ℕ}
    (hk : R.width ≤ k) (t : ℕ) : (tablesM R w t).time ≤ t * nodeCost (k + 1) := by
  induction t with
  | zero => simp only [tablesM, TimeM.time_pure, zero_mul, le_refl]
  | succ t ih =>
    simp only [tablesM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]
    have hb := R.width_le_iff.1 hk
    have := (stepCost_mono (hb (Fin.ofNat (n + 1) (n - t)))
      (hb (R.parent (Fin.ofNat (n + 1) (n - t))))).trans (stepCost_le_nodeCost (k + 1))
    rw [Nat.succ_mul]
    omega

/-- **Declared cost.** On a rooted decomposition with `n + 1` nodes (decomposition nodes, not
vertices of `G`) and width at most `k`, the declared cost of `mwisM` is at most
`(n + 1) · 2 ^ (k + 1) · (2 (k + 1) ^ 2 + 2 (k + 1) + 6)` ticks: linear in the number of nodes and
`2 ^ k · poly(k)` per node. The ticks are the declared per-node cost function of the module
docstring for an unformalized array implementation; they do not count the operations of `mwisM`
itself, whose evaluation as written is not FPT. The executable bound, with ticks charged inside the
loops of a program that materializes the tables, is `time_mwisFPT_le` in
`Complexity.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`. -/
theorem time_mwisM_le (R : G.RootedTreeDecomposition n) (w : V → ℕ) {k : ℕ}
    (hk : R.width ≤ k) : (mwisM R w).time ≤ (n + 1) * nodeCost (k + 1) := by
  simp only [mwisM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]
  have h1 := time_tablesM_le R w hk n
  have h2 := (rootCost_mono (R.width_le_iff.1 hk 0)).trans (rootCost_le_nodeCost (k + 1))
  rw [Nat.succ_mul]
  omega

end Charged

end Cslib.Algorithms.Lean.TreeDecomposition
