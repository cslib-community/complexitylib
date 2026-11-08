/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.GomoryHu.Basic
public import Complexity.Foundations.Combinatorics.SimpleGraph.Acyclic

/-!
# Gusfield's algorithm for Gomory–Hu trees

Gusfield ([Gusfield1990]) showed that a Gomory–Hu tree can be computed with `n - 1` minimum cut
computations in the original graph, without the contractions of Gomory and Hu's construction
([GomoryHu1961]). The tree is kept as a parent function `p` with root `r`. Initially every vertex
hangs from `r`. The other vertices `s` are processed once each: with `t = p s` and a minimum
`s`–`t` cut `X`, every other vertex whose parent is `t` and which lies in `X` is re-hung below `s`,
and if the parent of `t` lies in `X`, then `s` takes the place of `t` (`p s := p t`, `p t := s`).

This module states the algorithm for an arbitrary cut oracle and an arbitrary processing order,
and proves it correct for every symmetric submodular set function: if the oracle returns minimum
cuts, the final parent graph is a Gomory–Hu tree. The oracle may return any minimum cut. The
executable version over `Fin n` with Edmonds–Karp as the oracle, and its running time, are in
`Complexity.Algorithms.Lean.GomoryHu.Construction`.

## Proof

After processing a set `P ∋ r` of vertices, the invariant is: the parent of every vertex is in
`P`; every `i ∈ P` other than `r` carries a minimum `i`–`p i` cut `S i` that no other parent pointer
crosses (`z ∈ S i ↔ p z ∈ S i` for `z ≠ i`); and every vertex is joined to `r` by parent pointers.
To process `s ∉ P` with parent `t`, the cut `X` returned by the oracle is uncrossed with the sides,
away from `t`, of the parent edges at `t` (`IsMinCutBetween.union`, `IsMinCutBetween.sdiff`). This
gives a minimum `s`–`t` cut `U` that agrees with `X` on the vertices the algorithm inspects and
that no other parent pointer crosses. A re-hung vertex `i` keeps its label: a minimum `i`–`t` cut
missing `s` is a minimum `i`–`s` cut when some minimum `s`–`t` cut contains `i`. In the swap case,
`s` inherits the label of `t` and `t` gets `Uᶜ`; otherwise `s` gets `U`. Once every vertex is
processed, the parent graph is connected with `n - 1` edges, hence a tree, and by
`edgeSide_eq_of_forall_adj` the side of each parent edge `(u, p u)` containing `u` is `S u`.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.gusfieldStep`, `Cslib.Algorithms.Lean.GomoryHu.gusfieldLoop`,
  `Cslib.Algorithms.Lean.GomoryHu.gusfieldParent`: Gusfield's algorithm on parent functions, with
  a cut oracle `C : V → V → Finset V`.

The tree of the output is its parent graph `SimpleGraph.parentGraph`
(`Complexity.Foundations.Combinatorics.SimpleGraph.Acyclic`).

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gusfieldParent`: for a symmetric submodular `f`
  and an oracle returning minimum cuts, Gusfield's algorithm computes a Gomory–Hu tree of `f`.

## References

* [GomoryHu1961]
* [Gusfield1990]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.Submodular
open SimpleGraph (parentGraph parentGraph_adj edgeSide edgeSide_eq_of_forall_adj edgeSide_swap)

variable {V : Type*} {β : Type*}

/-! ### Iterated uncrossing -/

section IteratedUncross

variable [DecidableEq V] {ι : Type*}

/-- Uncross `X` successively with the sets `A k`, `k ∈ ks`: add `A k` when `a k ∈ X`, remove it
otherwise. -/
private def uncrossList (X : Finset V) (a : ι → V) (A : ι → Finset V) :
    List ι → Finset V
  | [] => X
  | k :: ks => if a k ∈ X then uncrossList X a A ks ∪ A k else uncrossList X a A ks \ A k

private theorem mem_uncrossList_of_mem {X : Finset V} {a : ι → V} {A : ι → Finset V} {ks : List ι}
    (hdisj : ks.Pairwise fun i j => Disjoint (A i) (A j)) {k : ι} (hk : k ∈ ks) {z : V}
    (hz : z ∈ A k) : z ∈ uncrossList X a A ks ↔ a k ∈ X := by
  induction ks with
  | nil => simp at hk
  | cons k' ks ih =>
    rw [List.pairwise_cons] at hdisj
    rcases List.mem_cons.mp hk with rfl | hk
    · unfold uncrossList
      split_ifs with h
      · exact iff_of_true (Finset.mem_union_right _ hz) h
      · exact iff_of_false (fun h' => (Finset.mem_sdiff.mp h').2 hz) h
    · have hz' : z ∉ A k' := fun h => Finset.disjoint_left.mp (hdisj.1 k hk) h hz
      unfold uncrossList
      split_ifs
      · rw [Finset.mem_union, ih hdisj.2 hk]
        simp [hz']
      · rw [Finset.mem_sdiff, ih hdisj.2 hk]
        simp [hz']

private theorem mem_uncrossList_of_forall_notMem {X : Finset V} {a : ι → V} {A : ι → Finset V}
    {ks : List ι} {z : V} (hz : ∀ k ∈ ks, z ∉ A k) : z ∈ uncrossList X a A ks ↔ z ∈ X := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hzk : z ∉ A k := hz k (by simp)
    have ih' := ih fun j hj => hz j (by simp [hj])
    unfold uncrossList
    split_ifs
    · rw [Finset.mem_union, ih']
      simp [hzk]
    · rw [Finset.mem_sdiff, ih']
      simp [hzk]

private theorem isMinCutBetween_uncrossList [Fintype V] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {s t : V} {X : Finset V} (hX : IsMinCutBetween f s t X) {a : ι → V}
    {A : ι → Finset V} {ks : List ι} (hA : ∀ k ∈ ks, IsMinCutBetween f (a k) t (A k))
    (hsA : ∀ k ∈ ks, s ∉ A k) (hdisj : ks.Pairwise fun i j => Disjoint (A i) (A j)) :
    IsMinCutBetween f s t (uncrossList X a A ks) := by
  induction ks with
  | nil => exact hX
  | cons k ks ih =>
    rw [List.pairwise_cons] at hdisj
    have ih' := ih (fun j hj => hA j (by simp [hj])) (fun j hj => hsA j (by simp [hj])) hdisj.2
    have hak : a k ∈ uncrossList X a A ks ↔ a k ∈ X := by
      refine mem_uncrossList_of_forall_notMem fun j hj h => ?_
      exact Finset.disjoint_left.mp (hdisj.1 j hj) (hA k (by simp)).left_mem h
    unfold uncrossList
    split_ifs with h
    · exact ih'.union hsub (hA k (by simp)) (hak.mpr h)
    · exact ih'.sdiff hsym hsub (hA k (by simp)) (fun h' => h (hak.mp h')) (hsA k (by simp))

end IteratedUncross

/-! ### Gusfield's algorithm -/

section Algorithm

variable [DecidableEq V]

/-- One step of Gusfield's algorithm ([Gusfield1990]) on the parent function `p`: given the
vertex `s` with current parent `t = p s` and an `s`–`t` cut `X ∋ s`, every other vertex with
parent `t` on the `s`-side of `X` is re-hung below `s`; if moreover the parent of `t` lies on the
`s`-side, `s` takes the place of `t` (`p s := p t`, `p t := s`). -/
@[expose] def gusfieldStep (p : V → V) (s : V) (X : Finset V) : V → V := fun z =>
  if z = s then (if p (p s) ∈ X then p (p s) else p s)
  else if z = p s then (if p (p s) ∈ X then s else p (p s))
  else if p z = p s ∧ z ∈ X then s else p z

/-- Gusfield's algorithm: process the vertices of `l` in order (skipping the root `r`), each
with one call `C s (p s)` of the cut oracle. -/
@[expose] def gusfieldLoop (C : V → V → Finset V) (r : V) : List V → (V → V) → V → V
  | [], p => p
  | s :: l, p => gusfieldLoop C r l (if s = r then p else gusfieldStep p s (C s (p s)))

/-- The parent function computed by Gusfield's algorithm with cut oracle `C`, root `r` and vertex
order `l`, starting from the star centred at `r`. -/
@[expose] def gusfieldParent (C : V → V → Finset V) (r : V) (l : List V) : V → V :=
  gusfieldLoop C r l fun _ => r

end Algorithm

/-! ### The invariant -/

section Invariant

/-- `x` and `y` are joined by a parent pointer. -/
private def TAdj (p : V → V) (x y : V) : Prop := p x = y ∨ p y = x

private theorem reflTransGen_tAdj_symm {p : V → V} {x y : V}
    (h : Relation.ReflTransGen (TAdj p) x y) : Relation.ReflTransGen (TAdj p) y x := by
  rw [← Relation.reflTransGen_swap]
  exact Relation.ReflTransGen.mono (fun _ _ h => Or.symm h) _ _ h

/-- Membership in a set closed under the parent pointers is constant along `TAdj` chains. -/
private theorem mem_iff_of_reflTransGen_tAdj {p : V → V} {Y : Finset V} (hY : ∀ z, z ∈ Y ↔ p z ∈ Y)
    {x y : V} (h : Relation.ReflTransGen (TAdj p) x y) : x ∈ Y ↔ y ∈ Y := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rcases hbc with h | h
    · rw [ih, hY, h]
    · rw [ih, ← h, ← hY]

variable [Fintype V] [DecidableEq V] [Preorder β]

/-- Invariant of Gusfield's algorithm after processing the vertex set `P ∋ r`: every processed
vertex `i ≠ r` has a parent `p i ∈ P` and a minimum `i`–`p i` cut `S i` that no other parent
pointer crosses, and all vertices are joined to `r` by parent pointers. -/
private structure GInv (f : Finset V → β) (r : V) (P : Finset V) (p : V → V) (S : V → Finset V) :
    Prop where
  root_mem : r ∈ P
  parent_root : p r = r
  parent_mem : ∀ z, p z ∈ P
  cut : ∀ i ∈ P, i ≠ r → IsMinCutBetween f i (p i) (S i)
  lam : ∀ i ∈ P, i ≠ r → ∀ z, z ≠ i → (z ∈ S i ↔ p z ∈ S i)
  conn : ∀ z, Relation.ReflTransGen (TAdj p) z r

omit [Fintype V] [DecidableEq V] in
private theorem gInv_init (f : Finset V → β) (r : V) (S : V → Finset V) :
    GInv f r {r} (fun _ => r) S where
  root_mem := Finset.mem_singleton_self r
  parent_root := rfl
  parent_mem _ := Finset.mem_singleton_self r
  cut _ hi hir := absurd (Finset.mem_singleton.mp hi) hir
  lam _ hi hir := absurd (Finset.mem_singleton.mp hi) hir
  conn _ := Relation.ReflTransGen.single (Or.inl rfl)

/-- Re-hanging a subtree: if `Si` is a minimum `i`–`t` cut missing `s` and `X` is a minimum
`s`–`t` cut containing `i`, then `Si` is a minimum `i`–`s` cut. -/
private theorem isMinCutBetween_rehang {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X) {i s t : V}
    {Si X : Finset V} (hSi : IsMinCutBetween f i t Si) (hX : IsMinCutBetween f s t X)
    (hsSi : s ∉ Si) (hiX : i ∈ X) : IsMinCutBetween f i s Si := by
  refine ⟨hSi.left_mem, hsSi, fun Y hi hs => ?_⟩
  by_cases htY : t ∈ Y
  · exact (hSi.le_of_separates hsym ⟨fun _ => hX.right_notMem, fun _ => hiX⟩).trans
      (hX.le_of_separates hsym ⟨fun h => absurd h hs, fun h => absurd htY h⟩)
  · exact hSi.le hi htY

/-- Swapping a vertex into the place of its parent: if `St` is a minimum `t`–`u` cut containing
`s`, and `X` is a minimum `s`–`t` cut containing `u`, then `St` is a minimum `s`–`u` cut. -/
private theorem isMinCutBetween_swap {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X) {s t u : V}
    {St X : Finset V} (hSt : IsMinCutBetween f t u St) (hX : IsMinCutBetween f s t X)
    (hsSt : s ∈ St) (huX : u ∈ X) : IsMinCutBetween f s u St := by
  refine ⟨hsSt, hSt.right_notMem, fun Y hs hu => ?_⟩
  by_cases htY : t ∈ Y
  · exact hSt.le htY hu
  · exact (hSt.le_of_separates hsym ⟨fun h => absurd h hX.right_notMem,
      fun h => absurd huX h⟩).trans (hX.le_of_separates hsym ⟨fun _ => htY, fun _ => hs⟩)

omit [Fintype V] [DecidableEq V] in
/-- Connectivity transfers along a change of parent function when every old parent pointer is
replaced by a chain of new ones. -/
private theorem reflTransGen_tAdj_of_step {p q : V → V} {r : V}
    (hp : ∀ z, Relation.ReflTransGen (TAdj p) z r)
    (h : ∀ z, Relation.ReflTransGen (TAdj q) z (p z)) (z : V) :
    Relation.ReflTransGen (TAdj q) z r := by
  have key : ∀ x y, TAdj p x y → Relation.ReflTransGen (TAdj q) x y := by
    rintro x y (hxy | hxy)
    · rw [← hxy]; exact h x
    · rw [← hxy]; exact reflTransGen_tAdj_symm (h y)
  exact Relation.reflTransGen_closed key _ _ (hp z)

end Invariant

/-! ### The step -/

section Step

variable [Fintype V] [DecidableEq V]

/-- The endpoint of the tree edge `(k, p k)` on the far side from `t`. -/
private def farEnd (p : V → V) (S : V → Finset V) (t k : V) : V := if t ∈ S k then p k else k

/-- The side of the tree edge `(k, p k)` away from `t`. -/
private def farSide (S : V → Finset V) (t k : V) : Finset V := if t ∈ S k then (S k)ᶜ else S k

/-! #### The processed tree edges at `t` -/

section EdgesAt

variable [Preorder β] {f : Finset V → β}

/-- The processed tree edges `(k, p k)` incident to `t`, named by their child endpoint `k`: the
children of `t` in `P` and, unless `t = r`, the edge from `t` to its parent. -/
private def edgesAt (r : V) (P : Finset V) (p : V → V) (t : V) : Finset V :=
  P.filter fun i => i ≠ r ∧ (p i = t ∨ i = t)

omit [Fintype V] in
private theorem mem_edgesAt {r : V} {P : Finset V} {p : V → V} {t k : V} :
    k ∈ edgesAt r P p t ↔ k ∈ P ∧ k ≠ r ∧ (p k = t ∨ k = t) := by
  simp [edgesAt]

omit [Fintype V] in
/-- The two kinds of tree edges at `t`: a child edge `(k, t)` with `t ∉ S k`, or the parent edge
`(t, p t)` with `t ∈ S t`. -/
private theorem GInv.edgesAt_cases {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    (I : GInv f r P p S) {t k : V} (hk : k ∈ edgesAt r P p t) :
    (t ∉ S k ∧ p k = t) ∨ (t ∈ S k ∧ k = t) := by
  obtain ⟨hkP, hkr, hkt⟩ := mem_edgesAt.mp hk
  have hc := I.cut k hkP hkr
  rcases hkt with h | h
  · exact .inl ⟨fun htk => hc.right_notMem (h ▸ htk), h⟩
  · exact .inr ⟨h ▸ hc.left_mem, h⟩

/-- The far side of a tree edge at `t` is a minimum cut between its far endpoint and `t`. -/
private theorem GInv.isMinCutBetween_farSide (hsym : ∀ X, f Xᶜ = f X) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} (I : GInv f r P p S) {t k : V} (hk : k ∈ edgesAt r P p t) :
    IsMinCutBetween f (farEnd p S t k) t (farSide S t k) := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  have hc := I.cut k hkP hkr
  rcases I.edgesAt_cases hk with ⟨htk, hpk⟩ | ⟨htk, hkt⟩
  · simp only [farEnd, farSide, htk, ↓reduceIte]
    rwa [hpk] at hc
  · simp only [farEnd, farSide, htk, ↓reduceIte]
    have hcc := hc.compl hsym
    rw [hkt] at hcc ⊢
    exact hcc

/-- Far sides are closed under the parent pointers other than their own edge. -/
private theorem GInv.mem_farSide_iff {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    (I : GInv f r P p S) {t k : V} (hk : k ∈ edgesAt r P p t) {z : V} (hzk : z ≠ k) :
    z ∈ farSide S t k ↔ p z ∈ farSide S t k := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  have hl := I.lam k hkP hkr z hzk
  unfold farSide
  split_ifs
  · rw [Finset.mem_compl, Finset.mem_compl, hl]
  · exact hl

/-- The child endpoint of a child edge `(k, t)` lies on its far side. -/
private theorem GInv.self_mem_farSide {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    (I : GInv f r P p S) {t k : V} (hk : k ∈ edgesAt r P p t) (htk : t ∉ S k) :
    k ∈ farSide S t k := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  simp only [farSide, htk, ↓reduceIte]
  exact (I.cut k hkP hkr).left_mem

/-- The parent of `t` lies on the far side of the parent edge `(t, p t)`. -/
private theorem GInv.parent_mem_farSide {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    (I : GInv f r P p S) {t : V} (htP : t ∈ P) (htr : t ≠ r) : p t ∈ farSide S t t := by
  have hc := I.cut t htP htr
  simp only [farSide, hc.left_mem, ↓reduceIte, Finset.mem_compl]
  exact hc.right_notMem

/-- The far sides of distinct tree edges at `t` are disjoint: a vertex on both would be joined to
`t` by parent pointers inside both, but `t` lies on neither. -/
private theorem GInv.disjoint_farSide (hsym : ∀ X, f Xᶜ = f X) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} (I : GInv f r P p S) {t k k' : V} (hk : k ∈ edgesAt r P p t)
    (hk' : k' ∈ edgesAt r P p t) (hne : k ≠ k') : Disjoint (farSide S t k) (farSide S t k') := by
  have htA : ∀ {j}, j ∈ edgesAt r P p t → t ∉ farSide S t j := fun hj =>
    (I.isMinCutBetween_farSide hsym hj).right_notMem
  -- The child endpoint of one edge is not on the far side of another.
  have hnot : ∀ {j j'}, j ∈ edgesAt r P p t → j' ∈ edgesAt r P p t → j ≠ j' →
      j ∉ farSide S t j' := by
    intro j j' hj hj' hjj' hmem
    rcases I.edgesAt_cases hj with ⟨-, hpj⟩ | ⟨-, hjt⟩
    · exact htA hj' (hpj ▸ (I.mem_farSide_iff hj' hjj').mp hmem)
    · exact htA hj' (hjt ▸ hmem)
  rw [Finset.disjoint_left]
  intro z hz hz'
  let Y := farSide S t k ∩ farSide S t k'
  have hY : ∀ x, x ∈ Y ↔ p x ∈ Y := by
    intro x
    simp only [Y, Finset.mem_inter]
    by_cases hxk : x = k
    · subst hxk
      have h2 : p x ∉ farSide S t k' := fun h => hnot hk hk' hne ((I.mem_farSide_iff hk' hne).mpr h)
      exact iff_of_false (fun h => hnot hk hk' hne h.2) (fun h => h2 h.2)
    by_cases hxk' : x = k'
    · subst hxk'
      have h2 : p x ∉ farSide S t k := fun h =>
        hnot hk' hk (Ne.symm hne) ((I.mem_farSide_iff hk (Ne.symm hne)).mpr h)
      exact iff_of_false (fun h => hnot hk' hk (Ne.symm hne) h.1) (fun h => h2 h.1)
    rw [I.mem_farSide_iff hk hxk, I.mem_farSide_iff hk' hxk']
  have hzt := mem_iff_of_reflTransGen_tAdj hY
    ((I.conn z).trans (reflTransGen_tAdj_symm (I.conn t)))
  exact htA hk (Finset.mem_inter.mp (hzt.mp (Finset.mem_inter.mpr ⟨hz, hz'⟩))).1

/-- **Coverage.** A vertex joined to `t` by parent pointers is `t`, an unprocessed child of `t`, or
on the far side of some tree edge at `t`. -/
private theorem GInv.cover {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    (I : GInv f r P p S) {t : V} (htP : t ∈ P) {w : V}
    (hw : Relation.ReflTransGen (TAdj p) w t) :
    (∃ k ∈ edgesAt r P p t, w ∈ farSide S t k) ∨ w = t ∨ (w ∉ P ∧ p w = t) := by
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inr (.inl rfl)
  | @head w c hwc _ ih =>
    rcases ih with ⟨k, hk, hck⟩ | hct | ⟨hcP, hpc⟩
    · -- `c` is on the far side of `(k, p k)`; so is `w` unless the step crosses that edge.
      by_cases hwk : w = k
      · subst hwk
        rcases I.edgesAt_cases hk with ⟨htk, -⟩ | ⟨-, hkt⟩
        · exact .inl ⟨w, hk, I.self_mem_farSide hk htk⟩
        · exact .inr (.inl hkt)
      rcases hwc with h | h
      · exact .inl ⟨k, hk, (I.mem_farSide_iff hk hwk).mpr (h ▸ hck)⟩
      · by_cases hck' : c = k
        · subst hck'
          rcases I.edgesAt_cases hk with ⟨-, hpk⟩ | ⟨htk, -⟩
          · exact .inr (.inl (h.symm.trans hpk))
          · obtain ⟨hcP, hcr, -⟩ := mem_edgesAt.mp hk
            simp only [farSide, htk, ↓reduceIte, Finset.mem_compl] at hck
            exact absurd (I.cut c hcP hcr).left_mem hck
        · exact .inl ⟨k, hk, h ▸ (I.mem_farSide_iff hk hck').mp hck⟩
    · -- `c = t`: `w` is a child of `t` or its parent.
      subst hct
      rcases hwc with h | h
      · by_cases hwP : w ∈ P
        · by_cases hwr : w = r
          · refine .inr (.inl ?_)
            rw [← h, hwr, I.parent_root]
          by_cases hwt : w = c
          · exact .inr (.inl hwt)
          have hwK : w ∈ edgesAt r P p c := mem_edgesAt.mpr ⟨hwP, hwr, .inl h⟩
          rcases I.edgesAt_cases hwK with ⟨htw, -⟩ | ⟨-, hwt'⟩
          · exact .inl ⟨w, hwK, I.self_mem_farSide hwK htw⟩
          · exact absurd hwt' hwt
        · exact .inr (.inr ⟨hwP, h⟩)
      · by_cases hwt : w = c
        · exact .inr (.inl hwt)
        have htr : c ≠ r := fun htr => hwt (by rw [← h, htr, I.parent_root])
        refine .inl ⟨c, mem_edgesAt.mpr ⟨htP, htr, .inr rfl⟩, ?_⟩
        rw [← h]
        exact I.parent_mem_farSide htP htr
    · -- `c` is an unprocessed child of `t`, hence a leaf: `w` is its parent `t`.
      rcases hwc with h | h
      · exact absurd (h ▸ I.parent_mem w) hcP
      · exact .inr (.inl (h ▸ hpc))

end EdgesAt

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β}

/-- **Uncrossing step of Gusfield's algorithm.** Given the invariant, an unprocessed vertex `s`
with parent `t = p s` and a minimum `s`–`t` cut `X`, there is a minimum `s`–`t` cut `U` that agrees
with `X` on the vertices whose parent is `t` and on the parent of `t`, and that no other parent
pointer crosses. -/
private theorem exists_uncrossed (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) {r : V}
    {P : Finset V} {p : V → V} {S : V → Finset V} (I : GInv f r P p S) {s t : V} (hsP : s ∉ P)
    (ht : p s = t) {X : Finset V} (hX : IsMinCutBetween f s t X) :
    ∃ U, IsMinCutBetween f s t U ∧ (∀ z, p z = t → (z ∈ U ↔ z ∈ X)) ∧
      (p t ∈ U ↔ p t ∈ X) ∧ (∀ z, z ≠ t → p z ≠ t → (z ∈ U ↔ p z ∈ U)) := by
  have htP : t ∈ P := ht ▸ I.parent_mem s
  let K := edgesAt r P p t
  let a := farEnd p S t
  let A := farSide S t
  have htA : ∀ k ∈ K, t ∉ A k := fun k hk => (I.isMinCutBetween_farSide hsym hk).right_notMem
  -- `s` is on no far side: it hangs from `t`, which is on none.
  have hsA : ∀ k ∈ K, s ∉ A k := by
    intro k hk hs
    have hsk : s ≠ k := fun h => hsP (h ▸ (mem_edgesAt.mp hk).1)
    exact htA k hk (ht ▸ (I.mem_farSide_iff hk hsk).mp hs)
  -- The uncrossed cut.
  let ks := K.toList
  have hks : ∀ k, k ∈ ks ↔ k ∈ K := fun k => Finset.mem_toList
  have hpw : ks.Pairwise fun i j => Disjoint (A i) (A j) :=
    (Finset.nodup_toList K).pairwise_of_forall_ne fun i hi j hj hij =>
      I.disjoint_farSide hsym ((hks i).mp hi) ((hks j).mp hj) hij
  let U := uncrossList X a A ks
  have U0 : IsMinCutBetween f s t U :=
    isMinCutBetween_uncrossList hsym hsub hX
      (fun k hk => I.isMinCutBetween_farSide hsym ((hks k).mp hk))
      (fun k hk => hsA k ((hks k).mp hk)) hpw
  have M1 : ∀ k ∈ K, ∀ z ∈ A k, (z ∈ U ↔ a k ∈ X) := fun k hk z hz =>
    mem_uncrossList_of_mem hpw ((hks k).mpr hk) hz
  have M2 : ∀ z, (∀ k ∈ K, z ∉ A k) → (z ∈ U ↔ z ∈ X) := fun z hz =>
    mem_uncrossList_of_forall_notMem fun k hk => hz k ((hks k).mp hk)
  refine ⟨U, U0, ?_, ?_, ?_⟩
  · -- A processed child `z` of `t` lies on its own far side, whose far end is `z`; an unprocessed
    -- one lies on no far side.
    intro z hz
    by_cases hzt : z = t
    · rw [hzt]
      exact iff_of_false U0.right_notMem hX.right_notMem
    by_cases hzP : z ∈ P
    · have hzr : z ≠ r := fun hzr => hzt (by rw [← hz, hzr, I.parent_root])
      have hzK : z ∈ K := mem_edgesAt.mpr ⟨hzP, hzr, .inl hz⟩
      rcases I.edgesAt_cases hzK with ⟨htz, -⟩ | ⟨-, hzt'⟩
      · rw [M1 z hzK z (I.self_mem_farSide hzK htz)]
        simp only [a, farEnd, htz, ↓reduceIte]
      · exact absurd hzt' hzt
    · refine M2 z fun k hk hzA => ?_
      have hzk : z ≠ k := fun h => hzP (h ▸ (mem_edgesAt.mp hk).1)
      exact htA k hk (hz ▸ (I.mem_farSide_iff hk hzk).mp hzA)
  · -- The parent of `t` lies on the far side of `(t, p t)`, whose far end is `p t`.
    by_cases htr : t = r
    · have : p t = t := by rw [htr, I.parent_root]
      rw [this]
      exact iff_of_false U0.right_notMem hX.right_notMem
    have htK : t ∈ K := mem_edgesAt.mpr ⟨htP, htr, .inr rfl⟩
    have htt : t ∈ S t := (I.cut t htP htr).left_mem
    rw [M1 t htK (p t) (I.parent_mem_farSide htP htr)]
    simp only [a, farEnd, htt, ↓reduceIte]
  · -- Any other `z` lies on the same far side as `p z`.
    intro z hzt hpz
    rcases I.cover htP ((I.conn z).trans (reflTransGen_tAdj_symm (I.conn t))) with
      ⟨k, hk, hzk⟩ | h | ⟨-, h⟩
    · have hzk' : z ≠ k := by
        intro h
        rcases (mem_edgesAt.mp hk).2.2 with h' | h'
        · exact hpz (h ▸ h')
        · exact hzt (h.trans h')
      rw [M1 k hk z hzk, M1 k hk (p z) ((I.mem_farSide_iff hk hzk').mp hzk)]
    · exact absurd h hzt
    · exact absurd h hpz

/-- **Gusfield's step preserves the invariant.** -/
private theorem gInv_step (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} (I : GInv f r P p S) {s : V} (hsP : s ∉ P) {X : Finset V}
    (hX : IsMinCutBetween f s (p s) X) :
    ∃ S', GInv f r (insert s P) (gusfieldStep p s X) S' := by
  obtain ⟨t, ht⟩ : ∃ t, p s = t := ⟨_, rfl⟩
  rw [ht] at hX
  obtain ⟨U, U0, U1, U2, U3⟩ := exists_uncrossed hsym hsub I hsP ht hX
  have htP : t ∈ P := ht ▸ I.parent_mem s
  have hst : s ≠ t := hX.ne
  have hsr : s ≠ r := fun h => hsP (h ▸ I.root_mem)
  have hsS : ∀ i ∈ P, i ≠ r → (s ∈ S i ↔ t ∈ S i) := fun i hi hir => by
    have := I.lam i hi hir s (fun h => hsP (h ▸ hi))
    rwa [ht] at this
  set q := gusfieldStep p s X with hq
  have qs : q s = if p t ∈ X then p t else t := by
    simp [hq, gusfieldStep, ht]
  have qt : q t = if p t ∈ X then s else p t := by
    simp [hq, gusfieldStep, Ne.symm hst, ht]
  have qz : ∀ z, z ≠ s → z ≠ t → q z = if p z = t ∧ z ∈ X then s else p z := by
    intro z hzs hzt
    simp [hq, gusfieldStep, hzs, ht, hzt]
  -- Vertices other than `s, t` keep their side of every set that `s, t` do not separate.
  have hgen : ∀ Y : Finset V, (s ∈ Y ↔ t ∈ Y) → ∀ z, z ≠ s → z ≠ t → (z ∈ Y ↔ p z ∈ Y) →
      (z ∈ Y ↔ q z ∈ Y) := by
    intro Y hY z hzs hzt hz
    rw [qz z hzs hzt]
    split_ifs with h
    · rw [hz, h.1, hY]
    · exact hz
  have hgenU : ∀ z, z ≠ s → z ≠ t → (z ∈ U ↔ q z ∈ U) := by
    intro z hzs hzt
    rw [qz z hzs hzt]
    split_ifs with h
    · exact iff_of_true ((U1 z h.1).mpr h.2) U0.left_mem
    · by_cases hpz : p z = t
      · have hzX : z ∉ X := fun hzX => h ⟨hpz, hzX⟩
        rw [hpz]
        exact iff_of_false (fun hzU => hzX ((U1 z hpz).mp hzU)) U0.right_notMem
      · exact U3 z hzt hpz
  -- Facts about the vertices other than `s` and `t`, shared by both cases.
  have hmem_other : ∀ z, z ≠ s → z ≠ t → q z ∈ insert s P := by
    intro z hzs hzt
    rw [qz z hzs hzt]
    split_ifs
    · exact Finset.mem_insert_self s P
    · exact Finset.mem_insert_of_mem (I.parent_mem z)
  have hcut_other : ∀ i ∈ P, i ≠ r → i ≠ s → i ≠ t → IsMinCutBetween f i (q i) (S i) := by
    intro i hiP hir his hit
    rw [qz i his hit]
    split_ifs with h
    · -- `i` is re-hung below `s`.
      have hc := I.cut i hiP hir
      rw [h.1] at hc
      refine isMinCutBetween_rehang hsym hc U0 ?_ ((U1 i h.1).mpr h.2)
      rw [hsS i hiP hir]
      exact hc.right_notMem
    · exact I.cut i hiP hir
  have hconn_other : ∀ z, z ≠ s → z ≠ t → TAdj q s t →
      Relation.ReflTransGen (TAdj q) z (p z) := by
    intro z hzs hzt hst'
    have hqz := qz z hzs hzt
    split_ifs at hqz with h
    · rw [h.1]
      exact (Relation.ReflTransGen.single (show TAdj q z s from Or.inl hqz)).tail hst'
    · exact Relation.ReflTransGen.single (Or.inl hqz)
  by_cases hswap : p t ∈ X
  · -- `s` takes the place of `t`.
    have htr : t ≠ r := by
      intro htr
      apply hX.right_notMem
      rw [htr, ← I.parent_root, ← htr]
      exact hswap
    have qs' : q s = p t := by rw [qs, ite_eq_left hswap]
    have qt' : q t = s := by rw [qt, ite_eq_left hswap]
    refine ⟨Function.update (Function.update S s (S t)) t Uᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_insert_of_mem I.root_mem
    · rw [qz r (Ne.symm hsr) (Ne.symm htr), ite_eq_right (fun h => ?_)]
      · exact I.parent_root
      · rw [I.parent_root] at h
        exact htr h.1.symm
    · intro z
      by_cases hzs : z = s
      · rw [hzs, qs']
        exact Finset.mem_insert_of_mem (I.parent_mem t)
      by_cases hzt : z = t
      · rw [hzt, qt']
        exact Finset.mem_insert_self s P
      exact hmem_other z hzs hzt
    · intro i hi hir
      by_cases his : i = s
      · rw [his, qs', Function.update_of_ne hst, Function.update_self]
        exact isMinCutBetween_swap hsym (I.cut t htP htr) U0 ((hsS t htP htr).mpr
          (I.cut t htP htr).left_mem) ((U2).mpr hswap)
      by_cases hit : i = t
      · rw [hit, qt', Function.update_self]
        exact U0.compl hsym
      have hiP : i ∈ P := (Finset.mem_insert.mp hi).resolve_left his
      rw [Function.update_of_ne hit, Function.update_of_ne his]
      exact hcut_other i hiP hir his hit
    · intro i hi hir z hzi
      by_cases his : i = s
      · rw [his, Function.update_of_ne hst, Function.update_self]
        rw [his] at hzi
        by_cases hzt : z = t
        · rw [hzt, qt']
          exact iff_of_true (I.cut t htP htr).left_mem
            ((hsS t htP htr).mpr (I.cut t htP htr).left_mem)
        · exact hgen (S t) (hsS t htP htr) z hzi hzt (I.lam t htP htr z hzt)
      by_cases hit : i = t
      · rw [hit, Function.update_self]
        rw [hit] at hzi
        by_cases hzs : z = s
        · rw [hzs, qs', Finset.mem_compl, Finset.mem_compl]
          exact iff_of_false (not_not.mpr U0.left_mem) (not_not.mpr (U2.mpr hswap))
        · simp only [Finset.mem_compl]
          exact not_congr (hgenU z hzs hzi)
      have hiP : i ∈ P := (Finset.mem_insert.mp hi).resolve_left his
      rw [Function.update_of_ne hit, Function.update_of_ne his]
      by_cases hzs : z = s
      · rw [hzs, qs', hsS i hiP hir]
        exact I.lam i hiP hir t (Ne.symm hit)
      by_cases hzt : z = t
      · rw [hzt, qt', hsS i hiP hir]
      exact hgen (S i) (hsS i hiP hir) z hzs hzt (I.lam i hiP hir z hzi)
    · refine reflTransGen_tAdj_of_step I.conn fun z => ?_
      by_cases hzs : z = s
      · rw [hzs, ht]
        exact Relation.ReflTransGen.single (Or.inr qt')
      by_cases hzt : z = t
      · rw [hzt]
        exact (Relation.ReflTransGen.single (show TAdj q t s from Or.inl qt')).tail
          (show TAdj q s (p t) from Or.inl qs')
      exact hconn_other z hzs hzt (Or.inr qt')
  · -- `s` is hung below `t`.
    have qs' : q s = t := by rw [qs, ite_eq_right hswap]
    have qt' : q t = p t := by rw [qt, ite_eq_right hswap]
    refine ⟨Function.update S s U, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_insert_of_mem I.root_mem
    · by_cases htr : r = t
      · rw [htr, qt', ← htr]
        exact I.parent_root
      · have hc : ¬(p r = t ∧ r ∈ X) := fun h => htr (I.parent_root ▸ h.1)
        rw [qz r (Ne.symm hsr) htr, ite_eq_right hc]
        exact I.parent_root
    · intro z
      by_cases hzs : z = s
      · rw [hzs, qs']
        exact Finset.mem_insert_of_mem htP
      by_cases hzt : z = t
      · rw [hzt, qt']
        exact Finset.mem_insert_of_mem (I.parent_mem t)
      exact hmem_other z hzs hzt
    · intro i hi hir
      by_cases his : i = s
      · rw [his, qs', Function.update_self]
        exact U0
      have hiP : i ∈ P := (Finset.mem_insert.mp hi).resolve_left his
      rw [Function.update_of_ne his]
      by_cases hit : i = t
      · rw [hit] at hir hiP ⊢
        rw [qt']
        exact I.cut t hiP hir
      exact hcut_other i hiP hir his hit
    · intro i hi hir z hzi
      by_cases his : i = s
      · rw [his, Function.update_self]
        rw [his] at hzi
        by_cases hzt : z = t
        · rw [hzt, qt']
          exact iff_of_false U0.right_notMem (fun h => hswap (U2.mp h))
        · exact hgenU z hzi hzt
      have hiP : i ∈ P := (Finset.mem_insert.mp hi).resolve_left his
      rw [Function.update_of_ne his]
      by_cases hzs : z = s
      · rw [hzs, qs']
        exact hsS i hiP hir
      by_cases hzt : z = t
      · rw [hzt, qt']
        exact I.lam i hiP hir t (fun h => hzi (hzt.trans h))
      exact hgen (S i) (hsS i hiP hir) z hzs hzt (I.lam i hiP hir z hzi)
    · refine reflTransGen_tAdj_of_step I.conn fun z => ?_
      by_cases hzs : z = s
      · rw [hzs, ht]
        exact Relation.ReflTransGen.single (Or.inl qs')
      by_cases hzt : z = t
      · rw [hzt]
        exact Relation.ReflTransGen.single (Or.inl qt')
      exact hconn_other z hzs hzt (Or.inl qs')

/-- Gusfield's loop preserves the invariant. -/
private theorem gInv_loop (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) {C : V → V → Finset V}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) {r : V} :
    ∀ (l : List V) {P : Finset V} {p : V → V} {S : V → Finset V}, GInv f r P p S → l.Nodup →
      (∀ x ∈ l, x ∉ P ∨ x = r) → ∃ S', GInv f r (P ∪ l.toFinset) (gusfieldLoop C r l p) S'
  | [], P, p, S, I, _, _ =>
    ⟨S, by rw [gusfieldLoop, List.toFinset_nil, Finset.union_empty]; exact I⟩
  | s :: l, P, p, S, I, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have hset : P ∪ (s :: l).toFinset = insert s P ∪ l.toFinset := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto
    by_cases hsr : s = r
    · have hl' : ∀ x ∈ l, x ∉ P ∨ x = r := fun x hx => hl x (List.mem_cons_of_mem s hx)
      obtain ⟨S', I'⟩ := gInv_loop hsym hsub hC l I hnd.2 hl'
      have hins : insert s P = P := Finset.insert_eq_of_mem (hsr ▸ I.root_mem)
      refine ⟨S', ?_⟩
      rw [hset, hins]
      rw [gusfieldLoop, ite_eq_left hsr]
      exact I'
    · have hsP : s ∉ P := (hl s (List.mem_cons_self)).resolve_right hsr
      have hsp : s ≠ p s := fun h => hsP (h ▸ I.parent_mem s)
      obtain ⟨S₁, I₁⟩ := gInv_step hsym hsub I hsP (hC s (p s) hsp)
      have hl' : ∀ x ∈ l, x ∉ insert s P ∨ x = r := by
        intro x hx
        rcases hl x (List.mem_cons_of_mem s hx) with h | h
        · left
          rw [Finset.mem_insert, not_or]
          exact ⟨fun hxs => hnd.1 (hxs ▸ hx), h⟩
        · exact Or.inr h
      obtain ⟨S', I'⟩ := gInv_loop hsym hsub hC l I₁ hnd.2 hl'
      refine ⟨S', ?_⟩
      rw [hset]
      rw [gusfieldLoop, ite_eq_right hsr]
      exact I'

end Step

/-! ### Correctness -/

section Correct

variable [Fintype V] [DecidableEq V] [Preorder β] {f : Finset V → β}

omit [DecidableEq V] in
/-- The side of a parent edge `(u, p u)` of the final tree is the label `S u`. -/
private theorem gInv_edgeSide_eq {r : V} {p : V → V} {S : V → Finset V}
    (I : GInv f r Finset.univ p S) (hT : (parentGraph p).IsTree) {u : V} (hur : u ≠ r)
    (hadj : (parentGraph p).Adj u (p u)) : edgeSide (parentGraph p) u (p u) = S u := by
  have hc := I.cut u (Finset.mem_univ u) hur
  refine edgeSide_eq_of_forall_adj hT hadj hc.left_mem hc.right_notMem fun x y hxy hne => ?_
  rcases (parentGraph_adj.mp hxy).2 with h | h
  · by_cases hxu : x = u
    · exact absurd (by rw [← h, hxu]) hne
    by_cases hxr : x = r
    · rw [← h, hxr, I.parent_root]
    rw [← h]
    exact I.lam u (Finset.mem_univ u) hur x hxu
  · by_cases hyu : y = u
    · exact absurd (by rw [← h, hyu, Sym2.eq_swap]) hne
    rw [← h]
    exact (I.lam u (Finset.mem_univ u) hur y hyu).symm

/-- **The final invariant yields a Gomory–Hu tree.** Once every vertex is processed, the parent
graph is a spanning tree whose parent edges carry the minimum cuts `S u`. -/
private theorem gInv_isGomoryHuTree (hsym : ∀ X, f Xᶜ = f X) {r : V} {p : V → V} {S : V → Finset V}
    (I : GInv f r Finset.univ p S) : IsGomoryHuTree f (parentGraph p) := by
  classical
  have hne : ∀ x, x ≠ r → p x ≠ x := fun x hx h =>
    (I.cut x (Finset.mem_univ x) hx).ne h.symm
  have hreach : ∀ x, (parentGraph p).Reachable x r := by
    intro x
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.reflTransGen_closed (fun a b hab => ?_) _ _ (I.conn x)
    by_cases heq : a = b
    · rw [heq]
    · exact Relation.ReflTransGen.single (parentGraph_adj.mpr ⟨heq, hab⟩)
  have hconn : (parentGraph p).Connected :=
    { preconnected := fun x y => (hreach x).trans (hreach y).symm
      nonempty := ⟨r⟩ }
  have hedge : (parentGraph p).edgeFinset =
      (Finset.univ.erase r).image fun i => s(i, p i) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parentGraph_adj, Finset.mem_image]
      constructor
      · rintro ⟨hxy, h | h⟩
        · refine ⟨x, Finset.mem_erase.mpr ⟨fun hxr => hxy ?_, Finset.mem_univ x⟩, by rw [h]⟩
          rw [← h, hxr, I.parent_root]
        · refine ⟨y, Finset.mem_erase.mpr ⟨fun hyr => hxy ?_, Finset.mem_univ y⟩, ?_⟩
          · rw [← h, hyr, I.parent_root]
          · rw [h, Sym2.eq_swap]
      · rintro ⟨i, hi, he⟩
        have hir := (Finset.mem_erase.mp hi).1
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(hne i hir).symm, Or.inl rfl⟩
        · exact ⟨hne i hir, Or.inr rfl⟩
  have hinj : Set.InjOn (fun i => s(i, p i)) ↑(Finset.univ.erase r) := by
    intro i hi j hj hij
    replace hi := (Finset.mem_erase.mp (Finset.mem_coe.mp hi)).1
    rcases Sym2.eq_iff.mp hij with ⟨h, -⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso
      have hc := I.cut i (Finset.mem_univ i) hi
      have hji : j ≠ i := fun h => hne i hi (h2.trans h)
      have hl := I.lam i (Finset.mem_univ i) hi j hji
      rw [← h1, ← h2] at hl
      exact hc.right_notMem (hl.mpr hc.left_mem)
  have htree : (parentGraph p).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hedge,
      Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ r),
      Finset.card_univ, Nat.card_eq_fintype_card]
    have := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  refine ⟨htree, fun u v huv => ?_⟩
  rcases (parentGraph_adj.mp huv).2 with h | h
  · have hur : u ≠ r := fun hur => (parentGraph_adj.mp huv).1 (by rw [← h, hur, I.parent_root])
    rw [← h] at huv ⊢
    rw [gInv_edgeSide_eq I htree hur huv]
    exact I.cut u (Finset.mem_univ u) hur
  · have hvr : v ≠ r := fun hvr => (parentGraph_adj.mp huv).1 (by rw [← h, hvr, I.parent_root])
    have hvu : (parentGraph p).Adj v (p v) := h ▸ huv.symm
    have hside := gInv_edgeSide_eq I htree hvr hvu
    rw [h] at hside
    rw [edgeSide_swap htree huv.symm, hside]
    have hc := I.cut v (Finset.mem_univ v) hvr
    rw [h] at hc
    exact hc.compl hsym

end Correct

/-- **Correctness of Gusfield's algorithm** ([Gusfield1990]). For a symmetric submodular `f`, a
cut oracle `C` returning a minimum `s`–`t` cut for all `s ≠ t`, a root `r` and a duplicate-free
list `l` containing every vertex other than `r`, the parent function computed by Gusfield's
algorithm is a Gomory–Hu tree of `f`. -/
theorem isGomoryHuTree_gusfieldParent [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) (r : V) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) : IsGomoryHuTree f (parentGraph (gusfieldParent C r l)) := by
  obtain ⟨S, I⟩ := gInv_loop hsym hsub hC l (gInv_init f r fun _ => ∅) hnd fun x _ => by
    by_cases hx : x = r
    · exact Or.inr hx
    · exact Or.inl (fun h => hx (Finset.mem_singleton.mp h))
  have huniv : ({r} : Finset V) ∪ l.toFinset = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, Finset.mem_univ,
      iff_true]
    by_cases hx : x = r
    · exact Or.inl hx
    · exact Or.inr (hl x hx)
  rw [huniv] at I
  exact gInv_isGomoryHuTree hsym I

end Cslib.Algorithms.Lean.GomoryHu
